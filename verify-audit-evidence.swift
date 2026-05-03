#!/usr/bin/env swift
//
// SnowbirdDays — offline audit-evidence verifier (Phase 4.5 P4.5-6A)
//
// Standalone Swift script with no SnowbirdDays target imports. Parses a
// `snowbirddays.auditEvidence` artifact and runs the integrity checks
// described by `AuditEvidenceExport`'s in-process verifier. Exits 0 on
// pass, non-zero on any failure with a single sanitized message on
// stderr.
//
// Usage:
//   swift scripts/verify-audit-evidence.swift --self-test
//   swift scripts/verify-audit-evidence.swift <path-to-artifact.json>
//
// The `--self-test` mode synthesizes a good artifact in-memory (deriving
// hashes from a fixed canonical payload), verifies it, then tampers with
// one byte and confirms the verifier rejects the tampered copy. It does
// not depend on any committed fixture files.
//
// This script is deliberately a separate implementation from the app's
// in-process verifier so a regression on either side fails closed: the
// auditor's tool and the app-side test harness must independently agree
// on what a valid artifact looks like.

import Foundation
import CryptoKit

// MARK: - Hex helpers

func hexLowercase(_ data: Data) -> String {
    let lut: [UInt8] = [
        0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
        0x38, 0x39, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66,
    ]
    var bytes = [UInt8]()
    bytes.reserveCapacity(data.count * 2)
    for b in data {
        bytes.append(lut[Int(b >> 4)])
        bytes.append(lut[Int(b & 0x0F)])
    }
    return String(decoding: bytes, as: UTF8.self)
}

func dataFromHex(_ hex: String) -> Data? {
    let chars = Array(hex.utf8)
    guard chars.count % 2 == 0 else { return nil }
    var out = Data(capacity: chars.count / 2)
    func nibble(_ c: UInt8) -> UInt8? {
        switch c {
        case 0x30...0x39: return c - 0x30
        case 0x41...0x46: return c - 0x41 + 10
        case 0x61...0x66: return c - 0x61 + 10
        default: return nil
        }
    }
    var i = 0
    while i < chars.count {
        guard let hi = nibble(chars[i]), let lo = nibble(chars[i + 1]) else { return nil }
        out.append((hi << 4) | lo)
        i += 2
    }
    return out
}

// MARK: - AnchorManifest canonical bytes

// Hand-built reconstruction of `AnchorManifest`'s CanonicalJSON output.
// Keys are emitted bytewise-sorted, integers as ASCII digits, byte
// blobs as lowercase hex, no whitespace. Sort order at the alphabet
// boundaries: c < d < e < h < m, and within "covered" the End vs Start
// suffix sorts End first because 'E' (0x45) < 'S' (0x53).
func canonicalAnchorManifestBytes(
    coveredSequenceStart: Int64,
    coveredSequenceEnd: Int64,
    dailyTailComponentHex: String,
    eventTailComponentHex: String
) -> Data {
    var s = "{"
    s += "\"coveredSequenceEnd\":\(coveredSequenceEnd),"
    s += "\"coveredSequenceStart\":\(coveredSequenceStart),"
    s += "\"dailyTailComponent\":\"\(dailyTailComponentHex)\","
    s += "\"eventTailComponent\":\"\(eventTailComponentHex)\","
    s += "\"hashAlgorithm\":\"SHA-256\","
    s += "\"manifestType\":\"snowbirddays.tsaAnchorManifest\","
    s += "\"manifestVersion\":1"
    s += "}"
    return Data(s.utf8)
}

// MARK: - Verifier

struct VerifyError: Error, CustomStringConvertible {
    let message: String
    var description: String { message }
}

func failv(_ msg: String) -> VerifyError { VerifyError(message: msg) }

func verify(jsonData: Data) throws {
    guard let raw = (try JSONSerialization.jsonObject(with: jsonData)) as? [String: Any] else {
        throw failv("artifact root is not a JSON object")
    }

    // Required top-level fields
    let requiredFields = [
        "artifactType", "formatVersion", "generatedAt", "disclaimer",
        "limitations", "metadata", "dailyAttestations",
        "ledgerBreakEvents", "anchorReceipts", "eventChainProof",
    ]
    for f in requiredFields {
        if raw[f] == nil { throw failv("missing top-level field: \(f)") }
    }

    guard let type = raw["artifactType"] as? String else {
        throw failv("artifactType must be a string")
    }
    guard type == "snowbirddays.auditEvidence" else {
        throw failv("wrong artifactType: \(type)")
    }
    guard let formatVersion = raw["formatVersion"] as? Int else {
        throw failv("formatVersion must be an integer")
    }
    guard formatVersion == 1 else {
        throw failv("unsupported formatVersion: \(formatVersion)")
    }

    let attestations = (raw["dailyAttestations"] as? [[String: Any]]) ?? []
    let receipts = (raw["anchorReceipts"] as? [[String: Any]]) ?? []
    let proofs = (raw["eventChainProof"] as? [[String: Any]]) ?? []

    try verifyDailyChain(attestations: attestations)
    try verifyReceipts(receipts: receipts, attestations: attestations)
    try verifyEventChainProof(proofs: proofs)
}

// MARK: - Daily chain

func verifyDailyChain(attestations: [[String: Any]]) throws {
    var prevSeq: Int64? = nil
    var prevHashHex: String? = nil
    let zeroHashHex = hexLowercase(Data(count: 32))

    for row in attestations {
        let seq = (row["sequenceNumber"] as? NSNumber)?.int64Value ?? -1
        let storedPrevHashHex = (row["previousHashHex"] as? String) ?? ""
        let storedHashHex = (row["canonicalPayloadHashHex"] as? String) ?? ""
        let payloadHex = (row["canonicalPayloadHex"] as? String) ?? ""

        guard let payloadBytes = dataFromHex(payloadHex) else {
            throw failv("malformed canonicalPayloadHex at sequence \(seq)")
        }
        let recomputed = hexLowercase(Data(SHA256.hash(data: payloadBytes)))
        guard recomputed == storedHashHex else {
            throw failv("canonicalPayloadHashHex != SHA256(canonicalPayloadHex) at sequence \(seq)")
        }

        // Full-store contract (LEARNINGS 2026-05-02): the artifact
        // carries every `DailyAttestation` row, so every gap or
        // non-1 starting sequence is a hard fail rather than a
        // partial-window tolerance.
        if let prev = prevSeq {
            if seq <= prev {
                throw failv("daily chain sequence \(seq) is out of order or duplicated")
            }
            if seq != prev + 1 {
                throw failv("daily chain has a gap: sequence \(seq) follows \(prev) but expected \(prev + 1)")
            }
            if let prevHash = prevHashHex, storedPrevHashHex != prevHash {
                throw failv("daily chain previousHash mismatch at sequence \(seq)")
            }
        } else {
            if seq != 1 {
                throw failv("daily chain first row must be sequence 1 (got sequence \(seq))")
            }
            if storedPrevHashHex != zeroHashHex {
                throw failv("daily chain genesis sequence \(seq) previousHash is not 32 zero bytes")
            }
        }

        try verifyCanonicalPayloadDuplicates(row: row, payloadBytes: payloadBytes,
                                             sequenceNumber: seq,
                                             storedPrevHashHex: storedPrevHashHex)

        prevSeq = seq
        prevHashHex = storedHashHex
    }
}

func verifyCanonicalPayloadDuplicates(
    row: [String: Any],
    payloadBytes: Data,
    sequenceNumber seq: Int64,
    storedPrevHashHex: String
) throws {
    guard let parsed = (try? JSONSerialization.jsonObject(with: payloadBytes)) as? [String: Any] else {
        throw failv("canonicalPayload bytes are not valid JSON at sequence \(seq)")
    }

    // sequenceNumber
    if let canSeq = (parsed["sequenceNumber"] as? NSNumber)?.int64Value, canSeq != seq {
        throw failv("canonicalPayload sequenceNumber mismatch at sequence \(seq)")
    }
    // dateKey
    if let canDate = parsed["dateKey"] as? String,
       canDate != (row["dateKey"] as? String ?? "") {
        throw failv("canonicalPayload dateKey mismatch at sequence \(seq)")
    }
    // jurisdiction
    if let canJur = parsed["jurisdiction"] as? String,
       canJur != (row["jurisdiction"] as? String ?? "") {
        throw failv("canonicalPayload jurisdiction mismatch at sequence \(seq)")
    }
    // serializerVersion / version
    let canonicalSer = (parsed["serializerVersion"] as? NSNumber)?.intValue
        ?? (parsed["version"] as? NSNumber)?.intValue
    if let cs = canonicalSer, cs != (row["serializerVersion"] as? Int ?? -1) {
        throw failv("canonicalPayload serializerVersion mismatch at sequence \(seq)")
    }
    // previousHash
    if let canPrev = parsed["previousHash"] as? String,
       canPrev.lowercased() != storedPrevHashHex.lowercased() {
        throw failv("canonicalPayload previousHash mismatch at sequence \(seq)")
    }
    // supersedesSequence
    if let canSup = parsed["supersedesSequence"] {
        let storedSup = (row["supersedesSequence"] as? NSNumber)?.int64Value
        if canSup is NSNull {
            if storedSup != nil {
                throw failv("canonicalPayload supersedesSequence mismatch at sequence \(seq)")
            }
        } else if let canSupNum = (canSup as? NSNumber)?.int64Value {
            if canSupNum != storedSup {
                throw failv("canonicalPayload supersedesSequence mismatch at sequence \(seq)")
            }
        }
    }
    // reattestReason
    if let canReat = parsed["reattestReason"] {
        let storedReat = row["reattestReason"] as? String
        if canReat is NSNull {
            if storedReat != nil {
                throw failv("canonicalPayload reattestReason mismatch at sequence \(seq)")
            }
        } else if let canReatStr = canReat as? String {
            if canReatStr != storedReat {
                throw failv("canonicalPayload reattestReason mismatch at sequence \(seq)")
            }
        }
    }
    // rawEventSequenceNumbers
    if let canSeqs = (parsed["rawEventSequenceNumbers"] as? [NSNumber])?.map({ $0.int64Value }) {
        let storedSeqs = ((row["rawEventSequenceNumbers"] as? [NSNumber])?.map { $0.int64Value }) ?? []
        if canSeqs.sorted() != storedSeqs.sorted() {
            throw failv("canonicalPayload rawEventSequenceNumbers mismatch at sequence \(seq)")
        }
    }
}

// MARK: - Receipts

func verifyReceipts(receipts: [[String: Any]], attestations: [[String: Any]]) throws {
    var receiptsById: [String: [String: Any]] = [:]
    for r in receipts {
        if let id = r["id"] as? String { receiptsById[id] = r }
    }
    var attestationBySeq: [Int64: [String: Any]] = [:]
    for a in attestations {
        if let seq = (a["sequenceNumber"] as? NSNumber)?.int64Value {
            attestationBySeq[seq] = a
        }
    }
    for r in receipts {
        let id = (r["id"] as? String) ?? ""
        let coveredStart = (r["coveredSequenceStart"] as? NSNumber)?.int64Value ?? 0
        let coveredEnd = (r["coveredSequenceEnd"] as? NSNumber)?.int64Value ?? 0
        let dailyTailHex = (r["dailyTailComponentHex"] as? String) ?? ""
        let eventTailHex = (r["eventTailComponentHex"] as? String) ?? ""
        let messageImprintHex = (r["messageImprintHashHex"] as? String) ?? ""

        let bytes = canonicalAnchorManifestBytes(
            coveredSequenceStart: coveredStart,
            coveredSequenceEnd: coveredEnd,
            dailyTailComponentHex: dailyTailHex,
            eventTailComponentHex: eventTailHex
        )
        let recomputed = hexLowercase(Data(SHA256.hash(data: bytes)))
        guard recomputed == messageImprintHex else {
            throw failv("messageImprintHashHex does not match recomputed AnchorManifest digest for receipt \(id)")
        }

        // Full-store contract (LEARNINGS 2026-05-02): every receipt
        // must have its covered-end attestation present in the
        // artifact. A missing covered-end is structural evidence the
        // artifact has been truncated or tampered with.
        guard let endRow = attestationBySeq[coveredEnd] else {
            throw failv("receipt \(id) coversSequenceEnd=\(coveredEnd) but the matching attestation is missing from the artifact")
        }
        let endHashHex = (endRow["canonicalPayloadHashHex"] as? String) ?? ""
        if dailyTailHex != endHashHex {
            throw failv("dailyTailComponentHex does not equal coveredSequenceEnd attestation hash for receipt \(id)")
        }
    }
    for a in attestations {
        let seq = (a["sequenceNumber"] as? NSNumber)?.int64Value ?? -1
        let status = (a["anchorStatus"] as? String) ?? "none"
        let receiptId = a["anchorReceiptId"] as? String
        guard status == "anchored", let rid = receiptId else { continue }
        guard let receipt = receiptsById[rid] else {
            throw failv("attestation \(seq) is anchored but receipt \(rid) is missing")
        }
        let coveredStart = (receipt["coveredSequenceStart"] as? NSNumber)?.int64Value ?? 0
        let coveredEnd = (receipt["coveredSequenceEnd"] as? NSNumber)?.int64Value ?? 0
        if seq < coveredStart || seq > coveredEnd {
            throw failv("attestation \(seq) is anchored but receipt \(rid) coverage does not include it")
        }
    }
}

// MARK: - Event chain proof

func verifyEventChainProof(proofs: [[String: Any]]) throws {
    var prevSeq: Int64? = nil
    var prevHashHex: String? = nil
    for row in proofs {
        let seq = (row["sequenceNumber"] as? NSNumber)?.int64Value ?? -1
        let ingestSealed = (row["ingestTimeHashed"] as? Bool) ?? false
        let prevHex = (row["previousEventHashHex"] as? String) ?? ""
        let hashHex = (row["eventHashHex"] as? String) ?? ""

        if ingestSealed {
            if prevHex.count != 64 {
                throw failv("eventChainProof sequence \(seq) previousEventHash is not 32 bytes")
            }
            if hashHex.count != 64 {
                throw failv("eventChainProof sequence \(seq) eventHash is not 32 bytes")
            }
        }
        // `VisitEventIngestSealer` links each sealed event to the
        // most recent prior sealed event regardless of numeric gap.
        // Mirror that contract: every proof row after the first
        // chains to the PREVIOUS EXPORTED proof row, not the
        // numerically-adjacent neighbor (LEARNINGS 2026-05-02).
        if let prev = prevSeq {
            if seq <= prev {
                throw failv("eventChainProof sequence \(seq) is out of order or duplicated")
            }
            if let prevHash = prevHashHex, prevHex != prevHash {
                throw failv("eventChainProof previousEventHash mismatch at sequence \(seq)")
            }
        }
        prevSeq = seq
        prevHashHex = hashHex
    }
}

// MARK: - Self-test fixture builder

/// Build the `(good, tampered)` JSON byte pair the self-test exercises.
/// Extracted so the same bytes back both `--self-test` and
/// `--write-fixtures <dir>`.
func buildSelfTestFixtures() throws -> (good: Data, tampered: Data) {
    // Synthesize a single canonical payload (the bytes do not need to
    // match production CanonicalJSON output exactly for the self-test;
    // the verifier only checks that SHA256(canonicalPayloadHex) ==
    // canonicalPayloadHashHex and that interior fields agree). Using a
    // valid JSON object ensures the duplicate-column check runs.
    let payloadBytes = Data(#"{"dateKey":"2026-04-30","jurisdiction":"US-FL","previousHash":"0000000000000000000000000000000000000000000000000000000000000000","sequenceNumber":1,"serializerVersion":1,"version":1}"#.utf8)
    let payloadHashBytes = Data(SHA256.hash(data: payloadBytes))
    let payloadHashHex = hexLowercase(payloadHashBytes)

    // Receipt covers sequence 1 with the daily tail equal to the
    // attestation's payload hash.
    let dailyTailHex = payloadHashHex
    let eventTailHex = hexLowercase(Data(repeating: 0xAB, count: 32))
    let manifestBytes = canonicalAnchorManifestBytes(
        coveredSequenceStart: 1,
        coveredSequenceEnd: 1,
        dailyTailComponentHex: dailyTailHex,
        eventTailComponentHex: eventTailHex
    )
    let messageImprintHex = hexLowercase(Data(SHA256.hash(data: manifestBytes)))

    let attestation: [String: Any] = [
        "sequenceNumber": NSNumber(value: Int64(1)),
        "dateKey": "2026-04-30",
        "jurisdiction": "US-FL",
        "serializerVersion": 1,
        "schemaVersion": 3,
        "previousHashHex": hexLowercase(Data(count: 32)),
        "canonicalPayloadHashHex": payloadHashHex,
        "canonicalPayloadHex": hexLowercase(payloadBytes),
        "anchorStatus": "anchored",
        "anchorReceiptId": "RCPT-SELFTEST",
        "rawEventSequenceNumbers": [NSNumber(value: Int64(10))],
    ]
    let receipt: [String: Any] = [
        "id": "RCPT-SELFTEST",
        "status": "verified",
        "coveredSequenceStart": NSNumber(value: Int64(1)),
        "coveredSequenceEnd": NSNumber(value: Int64(1)),
        "messageImprintHashHex": messageImprintHex,
        "dailyTailComponentHex": dailyTailHex,
        "eventTailComponentHex": eventTailHex,
        "tsaIdentifier": "freetsa",
        "tsaUrl": "https://freetsa.org/tsr",
        "submittedAt": "2026-05-01T00:00:00.000Z",
        "verifiedAt": NSNull(),
        "tsaTime": "2026-05-01T00:00:01.000Z",
    ]
    let proof: [String: Any] = [
        "sequenceNumber": NSNumber(value: Int64(10)),
        "ingestTimeHashed": true,
        "previousEventHashHex": hexLowercase(Data(count: 32)),
        "eventHashHex": hexLowercase(Data(repeating: 0xCD, count: 32)),
    ]
    let good: [String: Any] = [
        "artifactType": "snowbirddays.auditEvidence",
        "formatVersion": 1,
        "generatedAt": "2026-05-02T00:00:00.000Z",
        "disclaimer": "self-test fixture; do not redistribute",
        "limitations": ["self-test fixture"],
        "metadata": [
            "schemaVersion": 3,
            "dailyAttestationCount": 1,
            "ledgerBreakEventCount": 0,
            "anchorReceiptCount": 1,
            "eventChainProofCount": 1,
        ],
        "dailyAttestations": [attestation],
        "ledgerBreakEvents": [],
        "anchorReceipts": [receipt],
        "eventChainProof": [proof],
    ]
    let goodBytes = try JSONSerialization.data(withJSONObject: good, options: [.sortedKeys, .prettyPrinted])

    // Tamper with the canonicalPayloadHashHex by flipping one nibble.
    var tamperedAttestation = attestation
    var tamperedHash = payloadHashHex
    let flipIndex = tamperedHash.index(tamperedHash.startIndex, offsetBy: 0)
    let firstChar = tamperedHash[flipIndex]
    let flipped: Character = (firstChar == "0") ? "1" : "0"
    tamperedHash.replaceSubrange(flipIndex...flipIndex, with: String(flipped))
    tamperedAttestation["canonicalPayloadHashHex"] = tamperedHash

    var tamperedRoot = good
    tamperedRoot["dailyAttestations"] = [tamperedAttestation]
    let tamperedBytes = try JSONSerialization.data(withJSONObject: tamperedRoot, options: [.sortedKeys, .prettyPrinted])
    return (good: goodBytes, tampered: tamperedBytes)
}

// MARK: - Self-test

func selfTest() throws {
    let (goodBytes, tamperedBytes) = try buildSelfTestFixtures()
    try verify(jsonData: goodBytes)
    FileHandle.standardOutput.write(Data("self-test: good fixture verified\n".utf8))
    do {
        try verify(jsonData: tamperedBytes)
        FileHandle.standardError.write(Data("self-test FAILED: tampered fixture was not rejected\n".utf8))
        exit(1)
    } catch let err as VerifyError {
        FileHandle.standardOutput.write(Data("self-test: tampered fixture rejected (\(err.message))\n".utf8))
    }

    // Negative proof for daily-chain gap (LEARNINGS 2026-05-02). The
    // verifier must reject `1, 3` even when each row's canonical payload
    // hash is internally self-consistent.
    try selfTestRejectsDailyGap()
}

/// Build a `1, 3` gap artifact whose two attestations are individually
/// self-consistent (`SHA256(canonicalPayloadHex) == canonicalPayloadHashHex`)
/// and assert the verifier rejects it.
func selfTestRejectsDailyGap() throws {
    func attestationRow(seq: Int64, prevHashHex: String) -> [String: Any] {
        let json = "{\"dateKey\":\"2026-04-30\",\"jurisdiction\":\"US-FL\",\"previousHash\":\"\(prevHashHex)\",\"rawEventSequenceNumbers\":[],\"sequenceNumber\":\(seq),\"serializerVersion\":1,\"version\":1}"
        let payload = Data(json.utf8)
        let hash = Data(SHA256.hash(data: payload))
        return [
            "sequenceNumber": NSNumber(value: seq),
            "dateKey": "2026-04-30",
            "jurisdiction": "US-FL",
            "serializerVersion": 1,
            "schemaVersion": 3,
            "previousHashHex": prevHashHex,
            "canonicalPayloadHashHex": hexLowercase(hash),
            "canonicalPayloadHex": hexLowercase(payload),
            "anchorStatus": "none",
            "rawEventSequenceNumbers": [NSNumber](),
        ]
    }
    let zeroHashHex = hexLowercase(Data(count: 32))
    let row1 = attestationRow(seq: 1, prevHashHex: zeroHashHex)
    // The "previous" row 2 hash is irrelevant for the rejection: the
    // verifier should fail on the gap before checking link content.
    let bogusPrevHashHex = hexLowercase(Data(repeating: 0x77, count: 32))
    let row3 = attestationRow(seq: 3, prevHashHex: bogusPrevHashHex)
    let gap: [String: Any] = [
        "artifactType": "snowbirddays.auditEvidence",
        "formatVersion": 1,
        "generatedAt": "2026-05-02T00:00:00.000Z",
        "disclaimer": "self-test fixture; do not redistribute",
        "limitations": ["self-test fixture"],
        "metadata": [
            "schemaVersion": 3,
            "dailyAttestationCount": 2,
            "ledgerBreakEventCount": 0,
            "anchorReceiptCount": 0,
            "eventChainProofCount": 0,
        ],
        "dailyAttestations": [row1, row3],
        "ledgerBreakEvents": [],
        "anchorReceipts": [],
        "eventChainProof": [],
    ]
    let bytes = try JSONSerialization.data(withJSONObject: gap, options: [.sortedKeys, .prettyPrinted])
    do {
        try verify(jsonData: bytes)
        FileHandle.standardError.write(Data("self-test FAILED: daily 1,3 gap fixture was not rejected\n".utf8))
        exit(1)
    } catch let err as VerifyError {
        FileHandle.standardOutput.write(Data("self-test: 1,3 gap fixture rejected (\(err.message))\n".utf8))
    }
}

// MARK: - Fixture writer

func writeFixtures(toDirectory dir: String) throws {
    let (goodBytes, tamperedBytes) = try buildSelfTestFixtures()
    let fm = FileManager.default
    try fm.createDirectory(atPath: dir, withIntermediateDirectories: true)
    let goodURL = URL(fileURLWithPath: dir).appendingPathComponent("good.json")
    let tamperedURL = URL(fileURLWithPath: dir).appendingPathComponent("tampered.json")
    try goodBytes.write(to: goodURL)
    try tamperedBytes.write(to: tamperedURL)
    FileHandle.standardOutput.write(Data("wrote fixtures: \(goodURL.path), \(tamperedURL.path)\n".utf8))
}

// MARK: - Entry point

let args = CommandLine.arguments
if args.count == 2 && args[1] == "--self-test" {
    do {
        try selfTest()
        FileHandle.standardOutput.write(Data("self-test: PASS\n".utf8))
        exit(0)
    } catch {
        FileHandle.standardError.write(Data("self-test: FAIL: \(error)\n".utf8))
        exit(1)
    }
} else if args.count == 3 && args[1] == "--write-fixtures" {
    do {
        try writeFixtures(toDirectory: args[2])
        exit(0)
    } catch {
        FileHandle.standardError.write(Data("write-fixtures failed: \(error)\n".utf8))
        exit(1)
    }
} else if args.count == 2 {
    let path = args[1]
    let url = URL(fileURLWithPath: path)
    do {
        let data = try Data(contentsOf: url)
        try verify(jsonData: data)
        FileHandle.standardOutput.write(Data("verified: \(path)\n".utf8))
        exit(0)
    } catch let err as VerifyError {
        FileHandle.standardError.write(Data("verification failed: \(err.message)\n".utf8))
        exit(1)
    } catch {
        FileHandle.standardError.write(Data("verification failed: \(error)\n".utf8))
        exit(1)
    }
} else {
    FileHandle.standardError.write(Data("usage: verify-audit-evidence.swift --self-test\n       verify-audit-evidence.swift --write-fixtures <directory>\n       verify-audit-evidence.swift <artifact.json>\n".utf8))
    exit(2)
}
