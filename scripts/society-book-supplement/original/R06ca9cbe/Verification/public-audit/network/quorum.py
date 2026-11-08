"""Four pinned CAS journals; three signatures commit the exact original event.

Two quorums intersect in two members. With at most one lost/rolled-back signer,
one intersection member still retains its original CAS. Partitions may block,
but cannot authorize two competing histories. This is a fixed membership, single
writer journal, not a leader election or automatic membership-change protocol.
"""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import hashlib
from pathlib import Path

from cryptography.exceptions import InvalidSignature

from anchor import Client as AnchorClient, ZERO, ledger_hash, verify_commit
from crypto import digest

MEMBER_FAILURE = (OSError,EOFError,ValueError,KeyError,TypeError,AttributeError,InvalidSignature)


def membership(trust):
    if set(trust) != {"version","threshold","members"} or trust["version"] != 1 or trust["threshold"] != 3 or len(trust["members"]) != 4:
        raise ValueError("QUORUM_CONFIGURATION")
    members = trust["members"]
    if (len({entry["app"] for entry in members.values()}) != 4
            or len({entry["fingerprint"] for entry in members.values()}) != 4):
        raise ValueError("QUORUM_DUPLICATE_IDENTITY")
    return digest(trust)


def verify_certificate(trust, certificate, **binding):
    cluster = membership(trust)
    if (set(certificate) != {"kind","cluster","body","votes"} or certificate["kind"] != "anchor-quorum"
            or certificate["cluster"] != cluster or not 3 <= len(certificate["votes"]) <= 4):
        raise ValueError("QUORUM_CERTIFICATE")
    names = [entry["member"] for entry in certificate["votes"]]
    if names != sorted(set(names)):
        raise ValueError("QUORUM_DUPLICATE_VOTE")
    for vote in certificate["votes"]:
        if set(vote) != {"member","receipt"} or vote["member"] not in trust["members"] or vote["receipt"]["body"] != certificate["body"]:
            raise ValueError("QUORUM_VOTE_BINDING")
        verify_commit(trust["members"][vote["member"]],vote["receipt"],cluster=cluster,**binding)
    return certificate["body"]


class Client:
    def __init__(self, config):
        self.config = config
        self.trust = config["anchors"]["trust"]
        self.cluster = membership(self.trust)
        endpoints = config["anchors"]["endpoints"]
        if set(endpoints) != set(self.trust["members"]):
            raise ValueError("QUORUM_ENDPOINTS")
        if len({(entry["host"],entry["port"]) for entry in endpoints.values()}) != 4:
            raise ValueError("QUORUM_DUPLICATE_ENDPOINT")
        roots = [Path(entry["pki"]).resolve() for entry in endpoints.values()]
        if len(set(roots)) != 4 or len({hashlib.sha256((root / "ca.pem").read_bytes()).digest() for root in roots}) != 4:
            raise ValueError("QUORUM_SHARED_TLS_ROOT")
        self.nodes = {name:AnchorClient({**config,"anchor":{**entry,"identity":self.trust["members"][name],"cluster":self.cluster}})
                      for name,entry in endpoints.items()}
        self.entries = []

    def collect(self, operation, names=None, **values):
        # Every vote is authenticated by its own TLS root, transport identity,
        # app key and fresh nonce. Errors never become votes or empty genesis.
        names = list(self.nodes) if names is None else names
        results = {}
        with ThreadPoolExecutor(max_workers=4) as pool:
            jobs = {name:pool.submit(getattr(self.nodes[name],operation),**values) for name in names}
            for name,job in jobs.items():
                try:
                    results[name] = job.result()
                except MEMBER_FAILURE:
                    continue
        return results

    def certificate(self, receipts, *, seq, previous, message):
        if len(receipts) < 3:
            raise ValueError("QUORUM_UNAVAILABLE_RECONCILIATION_REQUIRED")
        point = dict(source=self.config["source"],stream=self.config["stream"],seq=seq,
                     head=ledger_hash(previous,message),previous=previous,message=digest(message),cluster=self.cluster)
        result = {"kind":"anchor-quorum","cluster":self.cluster,"body":point,
                  "votes":[{"member":name,"receipt":receipt} for name,receipt in sorted(receipts.items())]}
        verify_certificate(self.trust,result,source=self.config["source"],stream=self.config["stream"],
                           seq=seq,head=point["head"],previous=previous,message=message)
        return result

    def head(self):
        heads = self.collect("head")
        if len(heads) < 3:
            raise ValueError("QUORUM_UNAVAILABLE")
        for head in heads.values():
            if set(head) != {"source","stream","seq","head"} or type(head["seq"]) is not int or head["seq"] < 0:
                raise ValueError("QUORUM_HEAD")
        name = max(heads,key=lambda key:heads[key]["seq"])
        highest = heads[name]
        if len(self.entries) > highest["seq"]:
            raise ValueError("QUORUM_ROLLBACK")
        # A high signed head is a candidate, never a commit certificate. Fetch
        # its literal prefix, reject divergent peers, then obtain three fresh
        # exact CAS receipts before exposing that prefix to the service.
        entries = self.entries[:highest["seq"]]
        for seq in range(len(entries)+1,highest["seq"]+1):
            entries.append(self.nodes[name].get(seq))
        previous = ZERO
        for seq,entry in enumerate(entries,1):
            point = entry["receipt"]["body"]
            if point["seq"] != seq or point["previous"] != previous:
                raise ValueError("QUORUM_CHAIN")
            previous = point["head"]
        if previous != highest["head"]:
            raise ValueError("QUORUM_HEAD_BINDING")
        for member,head in heads.items():
            expected = ZERO if head["seq"] == 0 else entries[head["seq"]-1]["receipt"]["body"]["head"]
            if head["head"] != expected:
                raise ValueError("QUORUM_FORK")
        # Heal only exact prefixes. Nothing is overwritten; a stale member
        # must execute the same append validation and sign every original row.
        healthy = {}
        for member,head in heads.items():
            try:
                for seq in range(head["seq"]+1,highest["seq"]+1):
                    entry = entries[seq-1]
                    self.nodes[member].append(seq,entry["receipt"]["body"]["previous"],entry["message"])
                healthy[member] = highest
            except MEMBER_FAILURE:
                continue
        if len(healthy) < 3:
            raise ValueError("QUORUM_UNAVAILABLE_RECONCILIATION_REQUIRED")
        # At genesis the fresh matching read quorum itself is the evidence.
        if highest["seq"]:
            entry = entries[-1]
            if entry["receipt"]["kind"] != "anchor-quorum":
                receipts = self.collect("append",list(healthy),seq=highest["seq"],previous=entry["receipt"]["body"]["previous"],message=entry["message"])
                entry["receipt"] = self.certificate(receipts,seq=highest["seq"],previous=entry["receipt"]["body"]["previous"],message=entry["message"])
        self.entries = entries
        return highest

    def get(self, seq):
        if not 1 <= seq <= len(self.entries):
            raise ValueError("QUORUM_READ_HEAD_FIRST")
        entry = self.entries[seq-1]
        previous = entry["receipt"]["body"]["previous"]
        if entry["receipt"]["kind"] == "anchor-quorum":
            return entry
        fetched = self.collect("get",seq=seq)
        receipts = {name:value["receipt"] for name,value in fetched.items() if value["message"] == entry["message"]}
        return {"message":entry["message"],"receipt":self.certificate(receipts,seq=seq,previous=previous,message=entry["message"])}

    def append(self, seq, previous, message):
        receipts = self.collect("append",seq=seq,previous=previous,message=message)
        result = self.certificate(receipts,seq=seq,previous=previous,message=message)
        self.entries.append({"message":message,"receipt":result})
        return result
