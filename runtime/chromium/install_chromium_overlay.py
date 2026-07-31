#!/usr/bin/env python3

import argparse
import shutil
import subprocess
from pathlib import Path


PINNED_CHROMIUM_REVISION = "5e4202e0d22c4abf7400880edfd8553d063159df"


def replace_once(path: Path, old: str, new: str) -> None:
    contents = path.read_text()
    if new in contents:
        return
    if contents.count(old) != 1:
        raise RuntimeError(f"{path}: expected exactly one overlay insertion point")
    path.write_text(contents.replace(old, new))


def migrate_mitls_branding(path: Path) -> None:
    contents = path.read_text()
    migrated = (
        contents
        .replace("verified_mitls_client_socket", "atlas_client_socket")
        .replace("VerifiedMiTlsClientSocket", "AtlasClientSocket")
        .replace("Verified miTLS", "ATLAS")
        .replace("use-verified-mitls", "use-atlas")
        .replace("//third_party/mitls", "//third_party/atlas")
    )
    if migrated != contents:
        path.write_text(migrated)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Install the verified ATLAS provider in a Chromium checkout"
    )
    parser.add_argument(
        "--chromium-src", required=True, type=Path, help="Chromium src directory"
    )
    parser.add_argument(
        "--provider-archive",
        required=True,
        type=Path,
        help="ATLAS client engine static archive",
    )
    args = parser.parse_args()

    repository = Path(__file__).resolve().parents[2]
    chromium_src = args.chromium_src.resolve()
    revision = subprocess.check_output(
        ["git", "-C", str(chromium_src), "rev-parse", "HEAD"], text=True
    ).strip()
    if revision != PINNED_CHROMIUM_REVISION:
        raise RuntimeError(
            f"Chromium revision {revision} is not the pinned "
            f"{PINNED_CHROMIUM_REVISION}"
        )

    archive = args.provider_archive.resolve()
    if not archive.is_file():
        raise RuntimeError(
            f"{archive} is missing; run make -j$(nproc) atlas-client-provider"
        )

    overlay = repository / "runtime/chromium/chromium_src"
    copies = {
        overlay / "net/socket/atlas_client_socket.cc":
            chromium_src / "net/socket/atlas_client_socket.cc",
        overlay / "net/socket/atlas_client_socket.h":
            chromium_src / "net/socket/atlas_client_socket.h",
        overlay / "third_party/atlas/BUILD.gn":
            chromium_src / "third_party/atlas/BUILD.gn",
        repository / "runtime/chromium/tls13_client_socket.cc":
            chromium_src / "third_party/atlas/tls13_client_socket.cc",
        repository / "runtime/chromium/tls13_client_socket.h":
            chromium_src / "third_party/atlas/tls13_client_socket.h",
        repository / "runtime/tls13_client_engine.h":
            chromium_src / "third_party/atlas/tls13_client_engine.h",
        archive:
            chromium_src
            / "third_party/atlas/lib/libatlas_tls13_client_engine.a",
    }
    for source, destination in copies.items():
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)

    for path in (
        chromium_src / "net/BUILD.gn",
        chromium_src / "net/socket/client_socket_factory.cc",
        chromium_src / "content/browser/service_host/utility_process_host.cc",
    ):
        migrate_mitls_branding(path)

    replace_once(
        chromium_src / "net/BUILD.gn",
        '    "socket/ssl_client_socket_impl.h",\n',
        '    "socket/ssl_client_socket_impl.h",\n'
        '    "socket/atlas_client_socket.cc",\n'
        '    "socket/atlas_client_socket.h",\n',
    )
    replace_once(
        chromium_src / "net/BUILD.gn",
        '    "//third_party/rust/sfv/v0_15/wrapper",\n',
        '    "//third_party/rust/sfv/v0_15/wrapper",\n'
        '    "//third_party/atlas",\n',
    )

    factory = chromium_src / "net/socket/client_socket_factory.cc"
    replace_once(
        factory,
        '#include <utility>\n\n#include "base/no_destructor.h"\n',
        '#include <utility>\n\n'
        '#include "base/command_line.h"\n'
        '#include "base/logging.h"\n'
        '#include "base/no_destructor.h"\n',
    )
    replace_once(
        factory,
        '#include "net/socket/udp_client_socket.h"\n',
        '#include "net/socket/udp_client_socket.h"\n'
        '#include "net/socket/atlas_client_socket.h"\n',
    )
    replace_once(
        factory,
        "    return context->CreateSSLClientSocket(std::move(stream_socket),\n"
        "                                          host_and_port, ssl_config);\n",
        '    if (base::CommandLine::ForCurrentProcess()->HasSwitch(\n'
        '            "use-atlas")) {\n'
        '      LOG(WARNING) << "ATLAS provider selected for "\n'
        '                   << host_and_port.ToString();\n'
        '      return std::make_unique<AtlasClientSocket>(\n'
        '          context, std::move(stream_socket), host_and_port, ssl_config);\n'
        '    }\n'
        "    return context->CreateSSLClientSocket(std::move(stream_socket),\n"
        "                                          host_and_port, ssl_config);\n",
    )
    replace_once(
        chromium_src / "content/browser/service_host/utility_process_host.cc",
        "      switches::kIgnoreCertificateErrors,\n",
        "      switches::kIgnoreCertificateErrors,\n"
        '      "use-atlas",\n',
    )

    print(
        f"Installed verified ATLAS Chromium overlay at {revision} "
        f"in {chromium_src}"
    )


if __name__ == "__main__":
    main()
