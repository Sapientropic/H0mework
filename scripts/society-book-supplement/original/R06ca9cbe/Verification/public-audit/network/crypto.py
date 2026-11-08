"""Domain-separated messages over fixed-size TLS frames."""
from __future__ import annotations

import base64
from datetime import datetime, timedelta, timezone
import hashlib
import json
from pathlib import Path
import socket
import ssl

from cryptography import x509
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec, ed25519
from cryptography.x509.oid import ExtendedKeyUsageOID, NameOID, ObjectIdentifier

DOMAIN = b"public-source-audit/network/v1\x00"
APP_KEY = ObjectIdentifier("1.3.6.1.4.1.57264.2026.1")
FRAME = 16384
MAX_FRAMES = 4


def canonical(value) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False).encode()


def digest(value) -> str:
    return hashlib.sha256(canonical(value)).hexdigest()


def sign(key, kind: str, body: dict) -> dict:
    return {"kind": kind, "body": body,
            "signature": base64.b64encode(key.sign(DOMAIN + kind.encode() + b"\x00" + canonical(body))).decode()}


def verify(key, kind: str, message: dict) -> dict:
    if set(message) != {"kind", "body", "signature"} or message["kind"] != kind:
        raise ValueError("MESSAGE_KIND")
    key.verify(base64.b64decode(message["signature"], validate=True),
               DOMAIN + kind.encode() + b"\x00" + canonical(message["body"]))
    return message["body"]


def send(connection: ssl.SSLSocket, message: dict) -> None:
    encoded = canonical(message)
    if len(encoded) > MAX_FRAMES * FRAME - 4:
        raise ValueError("FRAME_TOO_LARGE")
    length = ((len(encoded) + 4 + FRAME - 1) // FRAME) * FRAME
    connection.sendall(len(encoded).to_bytes(4, "big") + encoded + bytes(length - 4 - len(encoded)))


def receive(connection: ssl.SSLSocket) -> dict:
    buffer = bytearray()
    while len(buffer) < FRAME:
        part = connection.recv(FRAME - len(buffer))
        if not part:
            raise EOFError("TRUNCATED_FRAME")
        buffer.extend(part)
    size = int.from_bytes(buffer[:4], "big")
    if size > MAX_FRAMES * FRAME - 4:
        raise ValueError("FRAME_ENCODING")
    length = ((size + 4 + FRAME - 1) // FRAME) * FRAME
    while len(buffer) < length:
        part = connection.recv(length - len(buffer))
        if not part:
            raise EOFError("TRUNCATED_FRAME")
        buffer.extend(part)
    if any(buffer[4 + size:]):
        raise ValueError("FRAME_ENCODING")
    return json.loads(buffer[4:4 + size])


def tls_context(profile: Path, *, server: bool) -> ssl.SSLContext:
    context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER if server else ssl.PROTOCOL_TLS_CLIENT)
    context.minimum_version = context.maximum_version = ssl.TLSVersion.TLSv1_3
    context.verify_mode = ssl.CERT_REQUIRED
    context.load_verify_locations(str(profile.parent / "ca.pem"))
    context.load_cert_chain(str(profile / "cert.pem"), str(profile / "tls.key"))
    # Constructing SSLContext directly keeps SSLKEYLOGFILE out of this protocol.
    context.keylog_filename = None
    if server:
        context.num_tickets = 0
    return context


def app_private(profile: Path):
    return serialization.load_pem_private_key((profile / "app.key").read_bytes(), password=None)


def peer(connection: ssl.SSLSocket):
    certificate = x509.load_der_x509_certificate(connection.getpeercert(binary_form=True))
    uri, = certificate.extensions.get_extension_for_class(x509.SubjectAlternativeName).value.get_values_for_type(x509.UniformResourceIdentifier)
    key = ed25519.Ed25519PublicKey.from_public_bytes(certificate.extensions.get_extension_for_oid(APP_KEY).value.value)
    return uri, certificate.fingerprint(hashes.SHA256()).hex(), key


def connect(profile: Path, port: int, *, hostname: str = "audit.local", host: str = "127.0.0.1") -> ssl.SSLSocket:
    raw = socket.create_connection((host, port), timeout=10)
    try:
        connection = tls_context(profile, server=False).wrap_socket(raw, server_hostname=hostname)
        connection.settimeout(30)
        if connection.version() != "TLSv1.3":
            raise ValueError("TLS_DOWNGRADE")
        return connection
    except BaseException:
        raw.close()
        raise


def create_pki(directory: Path, *, anchor: bool = False) -> dict:
    """Ephemeral local trust anchor, separate TLS and application signing keys."""
    directory.mkdir(mode=0o700)
    ca = ec.generate_private_key(ec.SECP256R1())
    name = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, "Source audit local test CA")])
    now = datetime.now(timezone.utc)
    certificate = (x509.CertificateBuilder().subject_name(name).issuer_name(name).public_key(ca.public_key())
                   .serial_number(x509.random_serial_number()).not_valid_before(now - timedelta(minutes=1))
                   .not_valid_after(now + timedelta(days=1)).add_extension(x509.BasicConstraints(ca=True, path_length=0), True)
                   .add_extension(x509.KeyUsage(False, False, False, False, False, True, True, None, None), True)
                   .sign(ca, hashes.SHA256()))
    (directory / "ca.pem").write_bytes(certificate.public_bytes(serialization.Encoding.PEM))
    registry = {}
    identities = [("server", "server"), ("auditor1", "1"), ("auditor2", "2"), ("rotated2", "2"), ("expired", "1")]
    if anchor:
        identities.append(("anchor", "anchor"))
    for label, actor in identities:
        profile = directory / label
        profile.mkdir(mode=0o700)
        tls = ec.generate_private_key(ec.SECP256R1())
        app = ed25519.Ed25519PrivateKey.generate()
        uri = "urn:public-audit:" + actor
        valid_from = now - timedelta(days=2) if label == "expired" else now - timedelta(minutes=1)
        valid_to = now - timedelta(days=1) if label == "expired" else now + timedelta(hours=1)
        sans = [x509.UniformResourceIdentifier(uri)]
        if actor in {"server", "anchor"}:
            sans += [x509.DNSName("anchor.local" if actor == "anchor" else "audit.local")]
        usages = [ExtendedKeyUsageOID.SERVER_AUTH] if actor in {"server", "anchor"} else [ExtendedKeyUsageOID.CLIENT_AUTH]
        if anchor and actor == "server":
            usages.append(ExtendedKeyUsageOID.CLIENT_AUTH)
        cert = (x509.CertificateBuilder().subject_name(x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, label)]))
                .issuer_name(name).public_key(tls.public_key()).serial_number(x509.random_serial_number())
                .not_valid_before(valid_from).not_valid_after(valid_to)
                .add_extension(x509.BasicConstraints(ca=False, path_length=None), True)
                .add_extension(x509.KeyUsage(True, False, False, False, False, False, False, None, None), True)
                .add_extension(x509.ExtendedKeyUsage(usages), False)
                .add_extension(x509.SubjectAlternativeName(sans), False)
                .add_extension(x509.UnrecognizedExtension(APP_KEY, app.public_key().public_bytes_raw()), False)
                .sign(ca, hashes.SHA256()))
        (profile / "cert.pem").write_bytes(cert.public_bytes(serialization.Encoding.PEM))
        for filename, key in (("tls.key", tls), ("app.key", app)):
            path = profile / filename
            path.write_bytes(key.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8, serialization.NoEncryption()))
            path.chmod(0o600)
        registry[label] = {"actor": actor, "fingerprint": cert.fingerprint(hashes.SHA256()).hex(), "app": app.public_key().public_bytes_raw().hex()}
    if anchor:
        for label, _ in identities:
            (directory / label / "anchor.json").write_text(json.dumps(registry["anchor"]))
    return registry
