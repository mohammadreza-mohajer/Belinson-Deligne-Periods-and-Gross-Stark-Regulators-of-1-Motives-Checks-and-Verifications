"""Build a reproducible source release with a fresh SHA-256 index."""
import argparse
import hashlib
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
ROOT_FILES = {
    ".gitattributes", ".gitignore", "BD.lean", "CITATION.md", "README.md",
    "lakefile.toml", "lake-manifest.json", "lean-toolchain",
}
DIRECTORIES = {".github", "BD", "docs", "inputs", "paper", "results", "scripts"}


def release_members():
    files = [ROOT / name for name in ROOT_FILES]
    for name in DIRECTORIES:
        base = ROOT / name
        for path in base.rglob("*"):
            if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc":
                files.append(path)
    data = {path.relative_to(ROOT).as_posix(): path.read_bytes() for path in files}
    checks = [hashlib.sha256(data[name]).hexdigest() + "  " + name for name in sorted(data)]
    data["SHA256SUMS"] = ("\n".join(checks) + "\n").encode("utf-8")
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="new .zip path outside the source directory")
    args = parser.parse_args()
    output = args.output.resolve()
    if output.suffix.lower() != ".zip" or output.is_relative_to(ROOT):
        parser.error("choose a .zip file outside the source directory")
    members = release_members()
    with zipfile.ZipFile(output, "x", compression=zipfile.ZIP_DEFLATED) as archive:
        for name, contents in sorted(members.items()):
            info = zipfile.ZipInfo(name, date_time=(2026, 1, 1, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            archive.writestr(info, contents, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    with zipfile.ZipFile(output) as archive:
        if archive.testzip() is not None or set(archive.namelist()) != set(members):
            raise ValueError("release archive failed verification")
    print(f"Packed {len(members)} files. SHA-256 {hashlib.sha256(output.read_bytes()).hexdigest()}")


if __name__ == "__main__":
    main()

