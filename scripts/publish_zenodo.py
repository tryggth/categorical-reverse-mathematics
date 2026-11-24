#!/usr/bin/env python3
"""Zenodo REST API publisher for Categorical Reverse Mathematics (draft, DOI, publish, versioning)."""
import argparse
import datetime
import json
import os
import pathlib
import subprocess
import sys
import urllib.error
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
DEFAULT_PDF = ROOT / "categorical_reverse_mathematics.pdf"
DRAFT_FILE = ROOT / ".zenodo_draft.json"
RECORD_FILE = ROOT / ".zenodo.json"
BASE_URL = "https://zenodo.org/api"
REPO = "tryggth/categorical-reverse-mathematics"


def load_token() -> str:
    """Load ZENODO_TOKEN from environment or ~/.env without ever printing it."""
    tok = os.environ.get("ZENODO_TOKEN", "").strip()
    if tok:
        return tok
    for env_path in (pathlib.Path.home() / ".env", ROOT / ".env"):
        if env_path.exists():
            for raw in env_path.read_text(encoding="utf-8").splitlines():
                line = raw.strip()
                if line.startswith("ZENODO_TOKEN="):
                    val = line.split("=", 1)[1].strip().strip('"').strip("'")
                    if val:
                        return val
    raise SystemExit("Missing ZENODO_TOKEN in environment or ~/.env")


def api_json(method: str, url: str, token: str, payload: dict | None = None) -> dict:
    """Execute a JSON REST request against the Zenodo API."""
    data = json.dumps(payload).encode("utf-8") if payload is not None else None
    headers = {
        "Authorization": f"Bearer {token}",
        "Accept": "application/json",
    }
    if data is not None:
        headers["Content-Type"] = "application/json"
    elif method == "POST":
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=data, headers=headers, method=method)
    try:
        with urllib.request.urlopen(req, timeout=60) as resp:
            body = resp.read().decode("utf-8")
            return json.loads(body) if body.strip() else {}
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"Zenodo HTTP {exc.code} on {method} {url}: {detail}") from None


def upload_to_bucket(bucket_url: str, pdf_path: pathlib.Path, token: str) -> dict:
    """Stream a PDF binary upload directly to a Zenodo deposition bucket URL."""
    payload = pdf_path.read_bytes()
    url = f"{bucket_url.rstrip('/')}/{pdf_path.name}"
    req = urllib.request.Request(
        url,
        data=payload,
        headers={
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/octet-stream",
            "Content-Length": str(len(payload)),
        },
        method="PUT",
    )
    try:
        with urllib.request.urlopen(req, timeout=180) as resp:
            body = resp.read().decode("utf-8")
            return json.loads(body) if body.strip() else {}
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"Zenodo upload HTTP {exc.code}: {detail}") from None


def build_metadata(version: str = "2.2", license_id: str = "cc-by-4.0") -> dict:
    return {
        "metadata": {
            "title": "Categorical Reverse Mathematics — Volume I: Obstructions, Residuums, and the Geometry of Necessity",
            "upload_type": "publication",
            "publication_type": "book",
            "publication_date": datetime.date.today().isoformat(),
            "creators": [
                {
                    "name": "Walters, James F.",
                    "affiliation": "Port Townsend, Washington",
                }
            ],
            "description": (
                "<p><strong>Categorical Reverse Mathematics — Volume I: Obstructions, Residuums, and the Geometry of Necessity</strong> "
                "develops a structural, geometric theory of deductive strength inside the 2-category of categorical "
                "doctrines. Evaluating Doctrinal Comparison Triples across Five Foundational Coordinate Axes "
                "(Choice/Splitting, Constructive Logic, Arithmetic Infinity, Characteristic/<em>p</em>-Torsion, and "
                "Directional Invertibility, extended in Chapter 7 along Axes VI–VII), the treatise establishes a "
                "tri-modal residuum calculus backed by eleven kernel-verified Lean 4 / mathlib4 modules "
                "(<code>HomotopyCRM</code>, 22,024 production lines, 152 blueprint declarations).</p>"
            ),
            "access_right": "open",
            "license": license_id,
            "version": version,
            "language": "eng",
            "keywords": [
                "categorical reverse mathematics",
                "topos theory",
                "category theory",
                "infinity-categories",
                "homotopy type theory",
                "constructive mathematics",
                "Lean 4",
                "mathlib4",
                "formal verification",
            ],
            "related_identifiers": [
                {
                    "identifier": f"https://github.com/{REPO}",
                    "relation": "isSupplementTo",
                    "resource_type": "software",
                }
            ],
            "prereserve_doi": True,
        }
    }


def cmd_create_draft(token: str) -> None:
    dep = api_json("POST", f"{BASE_URL}/deposit/depositions", token, {})
    dep_id = dep["id"]
    bucket_url = dep["links"]["bucket"]
    try:
        updated = api_json(
            "PUT",
            f"{BASE_URL}/deposit/depositions/{dep_id}",
            token,
            build_metadata(version="1.0.0", license_id="cc-by-4.0"),
        )
    except RuntimeError as err:
        if "license" in str(err).lower():
            updated = api_json(
                "PUT",
                f"{BASE_URL}/deposit/depositions/{dep_id}",
                token,
                build_metadata(version="1.0.0", license_id="cc-by"),
            )
        else:
            raise
    prereserve = updated.get("metadata", {}).get("prereserve_doi") or dep.get("metadata", {}).get("prereserve_doi") or {}
    doi = prereserve.get("doi")
    if not doi:
        raise RuntimeError(f"Zenodo did not return a prereserved DOI for draft {dep_id}")
    DRAFT_FILE.write_text(
        json.dumps(
            {
                "deposition_id": dep_id,
                "bucket_url": updated.get("links", {}).get("bucket", bucket_url),
                "doi": doi,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    print(f"Draft created: id={dep_id}, prereserved_doi={doi}")


def save_published_record(published: dict) -> None:
    links = published.get("links", {})
    record_url = links.get("record_html") or links.get("html") or f"https://zenodo.org/records/{published['id']}"
    RECORD_FILE.write_text(
        json.dumps(
            {
                "conceptrecid": str(published.get("conceptrecid", "")),
                "conceptdoi": published.get("conceptdoi", ""),
                "latest_record_id": published["id"],
                "latest_doi": published.get("doi", ""),
                "record_url": record_url,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


def cmd_upload_and_publish(token: str, pdf_path: pathlib.Path) -> None:
    if not DRAFT_FILE.exists():
        raise SystemExit(f"Missing draft metadata file: {DRAFT_FILE}")
    if not pdf_path.exists():
        raise SystemExit(f"Missing PDF file: {pdf_path}")
    draft = json.loads(DRAFT_FILE.read_text(encoding="utf-8"))
    dep_id = draft["deposition_id"]
    bucket_url = draft["bucket_url"]
    upload_to_bucket(bucket_url, pdf_path, token)
    published = api_json("POST", f"{BASE_URL}/deposit/depositions/{dep_id}/actions/publish", token)
    save_published_record(published)
    DRAFT_FILE.unlink(missing_ok=True)
    print(
        f"Published Zenodo record {published['id']}: doi={published.get('doi')}, "
        f"conceptdoi={published.get('conceptdoi')}"
    )


def cmd_new_version(token: str, pdf_path: pathlib.Path, version: str) -> None:
    if not RECORD_FILE.exists():
        raise SystemExit(f"Missing {RECORD_FILE}; publish initial record before minting versions.")
    if not pdf_path.exists():
        raise SystemExit(f"Missing PDF file: {pdf_path}")
    rec = json.loads(RECORD_FILE.read_text(encoding="utf-8"))
    rec_id = rec["latest_record_id"]
    ver_resp = api_json("POST", f"{BASE_URL}/deposit/depositions/{rec_id}/actions/newversion", token)
    draft_url = ver_resp["links"]["latest_draft"]
    draft = api_json("GET", draft_url, token)
    dep_id = draft["id"]
    bucket_url = draft["links"]["bucket"]
    for existing in draft.get("files", []):
        fid = existing["id"]
        api_json("DELETE", f"{BASE_URL}/deposit/depositions/{dep_id}/files/{fid}", token)
    upload_to_bucket(bucket_url, pdf_path, token)
    meta = dict(draft.get("metadata", {}))
    for transient in ("doi", "prereserve_doi"):
        meta.pop(transient, None)
    meta["version"] = version.lstrip("v")
    meta["publication_date"] = datetime.date.today().isoformat()
    api_json("PUT", f"{BASE_URL}/deposit/depositions/{dep_id}", token, {"metadata": meta})
    published = api_json("POST", f"{BASE_URL}/deposit/depositions/{dep_id}/actions/publish", token)
    save_published_record(published)
    print(
        f"Published Zenodo version {meta['version']} (record {published['id']}): "
        f"doi={published.get('doi')}, conceptdoi={published.get('conceptdoi')}"
    )


def cmd_sync_gh_secret(token: str) -> None:
    subprocess.run(
        ["gh", "secret", "set", "ZENODO_TOKEN", "--repo", REPO],
        input=token,
        text=True,
        check=True,
    )
    print(f"Synced ZENODO_TOKEN secret to {REPO}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--create-draft", action="store_true", help="Create unpublished draft and get prereserved DOI")
    ap.add_argument("--upload-and-publish", action="store_true", help="Upload PDF to draft and publish Zenodo record")
    ap.add_argument("--new-version", action="store_true", help="Publish a new version under existing Concept DOI")
    ap.add_argument("--sync-gh-secret", action="store_true", help="Store ZENODO_TOKEN in GitHub Actions secrets")
    ap.add_argument("--pdf", type=pathlib.Path, default=DEFAULT_PDF, help="Path to monograph PDF")
    ap.add_argument("--version", default="1.0.0", help="Version tag for --new-version")
    args = ap.parse_args()

    token = load_token()
    if args.create_draft:
        cmd_create_draft(token)
    elif args.upload_and_publish:
        cmd_upload_and_publish(token, args.pdf)
    elif args.new_version:
        cmd_new_version(token, args.pdf, args.version)
    elif args.sync_gh_secret:
        cmd_sync_gh_secret(token)
    else:
        ap.print_help()
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
