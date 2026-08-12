#!/usr/bin/env python3

import argparse
import datetime
import hashlib
import os
from pathlib import Path
import shutil
import struct
import subprocess
import tarfile
import tempfile


BUNDLE_NAME = "atlas-chromium-demo-linux-x86_64"
BUNDLE_NAME_LOGGING = "atlas-chromium-demo-logging-linux-x86_64"


def bundle_name(logging_enabled: bool) -> str:
    return BUNDLE_NAME_LOGGING if logging_enabled else BUNDLE_NAME

REQUIRED_CHROMIUM_FILES = (
    "chrome",
    "chrome_crashpad_handler",
    "chrome_100_percent.pak",
    "resources.pak",
    "headless_command_resources.pak",
    "icudtl.dat",
    "snapshot_blob.bin",
    "v8_context_snapshot.bin",
    "locales/en-US.pak",
)

OPTIONAL_CHROMIUM_FILES = (
    "chrome_200_percent.pak",
    "libEGL.so",
    "libGLESv2.so",
    "libvk_swiftshader.so",
    "vk_swiftshader_icd.json",
)

BUNDLE_FILES = (
    "README.md",
    "check-deps.sh",
    "start-server.sh",
    "launch-chrome.sh",
    "run-demo.sh",
)

EXECUTABLE_BUNDLE_FILES = (
    "check-deps.sh",
    "start-server.sh",
    "launch-chrome.sh",
    "run-demo.sh",
)


def run_output(command: list[str]) -> str:
    return subprocess.run(
        command,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    ).stdout.strip()


def require_x86_64_elf(path: Path) -> None:
    with path.open("rb") as source:
        header = source.read(20)
    if len(header) < 20 or header[:4] != b"\x7fELF":
        raise ValueError(f"{path} is not an ELF binary")
    if header[4] != 2 or header[5] != 1:
        raise ValueError(f"{path} is not a little-endian 64-bit ELF binary")
    if struct.unpack("<H", header[18:20])[0] != 62:
        raise ValueError(f"{path} is not an x86_64 ELF binary")


def copy_file(source: Path, destination: Path) -> None:
    if not source.is_file():
        raise FileNotFoundError(f"required bundle input is missing: {source}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)


def write_checksums(root: Path) -> None:
    lines = []
    for path in sorted(root.rglob("*")):
        if path.is_file() and path.name != "SHA256SUMS":
            hasher = hashlib.sha256()
            with path.open("rb") as source:
                while chunk := source.read(1024 * 1024):
                    hasher.update(chunk)
            digest = hasher.hexdigest()
            lines.append(f"{digest}  {path.relative_to(root).as_posix()}")
    (root / "SHA256SUMS").write_text("\n".join(lines) + "\n")


def normalized_tar_info(info: tarfile.TarInfo) -> tarfile.TarInfo:
    info.uid = 0
    info.gid = 0
    info.uname = "root"
    info.gname = "root"
    return info


def package_bundle(args: argparse.Namespace) -> None:
    chromium_out = args.chromium_out.resolve()
    bundle_sources = args.bundle_sources.resolve()
    output = args.output.resolve()
    bundle_directory = bundle_name(args.logging)

    for relative_path in REQUIRED_CHROMIUM_FILES:
        if not (chromium_out / relative_path).is_file():
            raise FileNotFoundError(
                f"required Chromium runtime asset is missing: "
                f"{chromium_out / relative_path}"
            )

    elf_inputs = [
        chromium_out / "chrome",
        chromium_out / "chrome_crashpad_handler",
        args.server.resolve(),
    ]
    elf_inputs.extend(
        chromium_out / path
        for path in OPTIONAL_CHROMIUM_FILES
        if path.endswith(".so") and (chromium_out / path).is_file()
    )
    for path in elf_inputs:
        require_x86_64_elf(path)

    output.parent.mkdir(parents=True, exist_ok=True)
    if output.exists():
        output.unlink()

    with tempfile.TemporaryDirectory(
        prefix=f".{bundle_directory}-", dir=output.parent
    ) as temporary_directory:
        root = Path(temporary_directory) / bundle_directory
        chromium_destination = root / "chromium"
        server_destination = root / "server"

        for relative_path in REQUIRED_CHROMIUM_FILES:
            copy_file(
                chromium_out / relative_path,
                chromium_destination / relative_path,
            )
        for relative_path in OPTIONAL_CHROMIUM_FILES:
            source = chromium_out / relative_path
            if source.is_file():
                copy_file(source, chromium_destination / relative_path)

        copy_file(args.server.resolve(), server_destination / "openssl_http_server")
        copy_file(args.certificate.resolve(), server_destination / "chain.pem")
        copy_file(args.private_key.resolve(), server_destination / "leaf.key")

        for relative_path in BUNDLE_FILES:
            copy_file(bundle_sources / relative_path, root / relative_path)
        for relative_path in EXECUTABLE_BUNDLE_FILES:
            (root / relative_path).chmod(0o755)
        copy_file(
            args.trace_analyzer.resolve(),
            root / "analyze-atlas-trace.py",
        )
        (root / "analyze-atlas-trace.py").chmod(0o755)
        (server_destination / "openssl_http_server").chmod(0o755)
        (chromium_destination / "chrome").chmod(0o755)
        (chromium_destination / "chrome_crashpad_handler").chmod(0o755)
        (server_destination / "leaf.key").chmod(0o600)

        repository_revision = run_output(
            ["git", "-C", str(args.repository.resolve()), "describe", "--always", "--dirty"]
        )
        chromium_revision = run_output(
            ["git", "-C", str(args.chromium_source.resolve()), "rev-parse", "HEAD"]
        )
        build_time = datetime.datetime.now(datetime.timezone.utc).isoformat()
        (root / "BUILD_INFO").write_text(
            f"Bundle: {bundle_directory}\n"
            f"Architecture: Linux x86_64\n"
            f"Created: {build_time}\n"
            f"ATLAS revision: {repository_revision}\n"
            f"Chromium revision: {chromium_revision}\n"
            f"ATLAS logging: {'enabled' if args.logging else 'disabled'}\n"
        )

        dependency_sections = []
        for name, path in (
            ("Chromium", chromium_destination / "chrome"),
            ("Crashpad handler", chromium_destination / "chrome_crashpad_handler"),
            ("HTTPS demo server", server_destination / "openssl_http_server"),
        ):
            dependency_sections.append(f"## {name}\n{run_output(['ldd', str(path)])}")
        (root / "SYSTEM_LIBRARIES.txt").write_text(
            "\n\n".join(dependency_sections) + "\n"
        )

        write_checksums(root)

        with tarfile.open(output, "w:gz", compresslevel=1) as archive:
            archive.add(
                root,
                arcname=bundle_directory,
                recursive=True,
                filter=normalized_tar_info,
            )

    print(output)


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Package the verified ATLAS Chromium HTTPS demo"
    )
    parser.add_argument("--repository", required=True, type=Path)
    parser.add_argument("--chromium-source", required=True, type=Path)
    parser.add_argument("--chromium-out", required=True, type=Path)
    parser.add_argument("--server", required=True, type=Path)
    parser.add_argument("--certificate", required=True, type=Path)
    parser.add_argument("--private-key", required=True, type=Path)
    parser.add_argument("--bundle-sources", required=True, type=Path)
    parser.add_argument("--trace-analyzer", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument(
        "--logging",
        action="store_true",
        help="package a bundle built with ATLAS_LOGGING=1; names the bundle "
        "directory distinctly and records the fact in BUILD_INFO",
    )
    return parser.parse_args()


if __name__ == "__main__":
    package_bundle(parse_arguments())
