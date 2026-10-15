# Security Domain Getting Started

This guide continues directly from
[Rustlets Getting Started](rustlets.getting.started.md). It keeps the same
Pico1, SWD probe, UART link, `apdu-tool`, and `my_first_rustlet.fae`, but moves
administration from the open development root to a Rustlet-backed Security
Domain using SCP03.

The goal here is operational: preinstall a Security Domain, open its secure
channel, inspect it, deploy the Rustlet built in the previous guide under its
authority, and verify persistence. To implement your own SCP03 Security Domain,
continue afterwards with
[Rustlet Security Domain Getting Started](rustlet.security.domain.getting.started.md).

> The keys in this tutorial are public test values. Never reuse them for a
> product, personal device, or any data that matters.

## 1. Understand The Image Change

The earlier development image used an open root. This guide builds a new image
with:

- no kernel-native secure-channel protocol (`protocols = []`);
- `complete_security_domain` preinstalled as the root Security Domain;
- root instance AID `A0000047504F5304`;
- one development SCP03 S16 keyset owned by that instance.

The kernel still owns transport, registry integrity, hierarchy, lifecycle, and
base privilege checks. The Rustlet Security Domain owns SCP03 discovery,
establishment, protected APDU processing, and its additional policy.

Flashing this image erases the Pico1's 2 MiB flash, including the registry from
the preceding exercise. Keep `my_first_rustlet.fae`: it will be deployed again
through the protected management path.

## 2. Prepare The Image, Client, And Keys

If necessary, rebuild the Rustlet created in the preceding guide:

```bash
cd rustlets/my_first_rustlet
RUSTLET_TARGET=thumbv6m-none-eabi cargo build-fae
cd ../..
```

From the repository root, build the Security Domain image and APDU client:

```bash
cargo run -- build \
  --config configs/config_security_domain_getting_started.toml \
  raspi-pico1
cargo build -p apdu_tool
```

Create a local key file. `umask 077` prevents newly created files from being
readable by other users:

```bash
umask 077
printf '%s\n' \
  'version = 1' \
  'id = 3' \
  'profile = "s16"' \
  'enc = "404142434445464748494A4B4C4D4E4F"' \
  'mac = "505152535455565758595A5B5C5D5E5F"' \
  > getting-started-scp03.toml
```

Do not commit this file. It matches the deliberately public development keys
in `configs/config_security_domain_getting_started.toml`.

## 3. Flash The Pico1 And Capture Its ATR

Connect the Pico1 exactly as in the previous guide. In the first terminal,
start the UART client before releasing reset:

```bash
target/debug/apdu_tool -v \
  --serial /dev/cu.usbmodemXXXX:115200 \
  --connect-timeout 120s --atr-timeout infinite atr
```

Replace the serial device with the one connected to GPIO0/GPIO1. On Linux it
will commonly be `/dev/ttyACM0`.

In the second terminal, program and start the image:

```bash
openocd \
  -f interface/cmsis-dap.cfg \
  -f target/rp2040.cfg \
  -c "adapter speed 1000" \
  -c init \
  -c "reset init" \
  -c "flash erase_address 0x10000000 0x200000" \
  -c "flash write_image {target/kernel/firmware/kernel.elf}" \
  -c "verify_image {target/kernel/firmware/kernel.elf}" \
  -c "reset run" \
  -c shutdown
```

At 1 MHz, the validated write takes only a few seconds. You can adjust
`adapter speed` if your probe or wiring needs a different value; OpenOCD's
default is often deliberately slow.

The ATR creates `session.json` in the current directory. Keep all following
`apdu-tool` commands there. The ATR's native SCP bitmap is empty in this image:
that is expected, because SCP03 is delegated to the Rustlet Security Domain.

## 4. Select And Discover The Security Domain

Select the root instance, then ask the selected authority for its recognition
and capability data:

```bash
target/debug/apdu_tool select A0000047504F5304
target/debug/apdu_tool gp get-data card-recognition --format tlv
target/debug/apdu_tool gp get-data card-capabilities --format tlv
```

Each command must end with `9000`. `apdu-tool` automatically retries a T=0
`6Cxx` response with the exact length requested by the card. The capability
response now advertises SCP03 through the selected Rustlet Security Domain,
even though the kernel's ATR advertised no native protocol.

## 5. Open SCP03

Open an encrypted and authenticated command channel:

```bash
target/debug/apdu_tool scp03 open \
  --scp03-profile s16 \
  --security-domain A0000047504F5304 \
  --security-level c-mac+c-enc \
  --keyset getting-started-scp03.toml
target/debug/apdu_tool scp03 inspect
```

`scp03 open` performs INITIALIZE UPDATE and EXTERNAL AUTHENTICATE. It stores
derived session keys, counters, and MAC chains in the local `session.json` with
mode `0600`. Subsequent `gp`, `select`, and `raw` commands resume this channel;
their command lines describe clear APDUs, while the client applies and checks
secure messaging.

## 6. Deploy The Rustlet Under The Security Domain

Deploy the FAE built in the preceding guide and name the selected Security
Domain explicitly as its owner:

```bash
target/debug/apdu_tool --progress gp deploy \
  A0000047504F5321 \
  rustlets/my_first_rustlet/build/my_first_rustlet.fae \
  A0000047504F5322 \
  --security-domain A0000047504F5304
```

The last response must be `9000`. Inspect the two new objects with filtered
queries (filtering also keeps this first reading concise):

```bash
target/debug/apdu_tool gp get-status packages --aid A0000047504F5321
target/debug/apdu_tool gp get-status applications --aid A0000047504F5322
```

Both records identify `A0000047504F5304` as their parent Security Domain.
Select the instance and exercise the code written in the earlier guide:

```bash
target/debug/apdu_tool select A0000047504F5322
target/debug/apdu_tool raw 00:04:00:00:00:02
target/debug/apdu_tool raw 00:08:00:00:04:04:DE:AD:BE:EF
```

Expected response data is respectively `CA FE` and `DE AD BE EF`, with status
`9000` in both cases. The Rustlet APDUs are protected by the owning Security
Domain's live channel.

## 7. Verify Persistence After Reset

Close the host-side channel and wait for a fresh ATR:

```bash
target/debug/apdu_tool close
target/debug/apdu_tool -v \
  --serial /dev/cu.usbmodemXXXX:115200 \
  --connect-timeout 120s --atr-timeout infinite atr
```

While that command waits, reset without erasing or reflashing:

```bash
openocd \
  -f interface/cmsis-dap.cfg \
  -f target/rp2040.cfg \
  -c "adapter speed 1000" \
  -c init -c "reset run" -c shutdown
```

Reopen SCP03, then select and call the installed Rustlet again:

```bash
target/debug/apdu_tool scp03 open \
  --scp03-profile s16 \
  --security-domain A0000047504F5304 \
  --security-level c-mac+c-enc \
  --keyset getting-started-scp03.toml
target/debug/apdu_tool select A0000047504F5322
target/debug/apdu_tool raw 00:04:00:00:00:02
```

Receiving `CA FE 90 00` proves that the registry objects survived reset. A new
SCP03 session was established; live secure-channel state itself is never
reused across reset.

## 8. Deploy A Supplementary Security Domain

The minimal `simple_security_domain` is useful for seeing how a Security Domain
FAE differs from an ordinary application. Build it for Pico1:

```bash
cd rustlets/simple_security_domain
RUSTLET_TARGET=thumbv6m-none-eabi cargo build-fae
cd ../..
```

Deploy it through the open SCP03 session. A Security Domain FAE must explicitly
request the `security-domain` privilege; this example also asks for delegated
management:

```bash
target/debug/apdu_tool --progress gp deploy \
  A0000047504F5330 \
  rustlets/simple_security_domain/build/simple_security_domain.fae \
  A0000047504F5331 \
  --security-domain A0000047504F5304 \
  --privileges security-domain,delegated-management
target/debug/apdu_tool gp get-status applications --aid A0000047504F5331
target/debug/apdu_tool select A0000047504F5331
```

This proves protected loading, Security Domain registration, privilege
validation, and selection. It does **not** make the neutral example
cryptographically usable: `simple_security_domain` advertises no protocol and
there is not yet a supported first-key provisioning flow for a dynamically
created Rustlet Security Domain in this beta. The next guide therefore develops
and validates a custom SCP03 implementation as a preinstalled root, whose keys
are provisioned by the image manifest.

## 9. Preinstallation, Dynamic Deployment, And The Oracle Test

Use preinstallation when the initial trust hierarchy and keys are part of a
known firmware composition. Use dynamic deployment for packages and instances
authorized later through a live Security Domain. The configuration used here
is intentionally small and readable; the broader predeployment fixture is
[`config_predeployment_test.toml`](../configs/config_predeployment_test.toml).

The checked-in hardware oracle for the delegated SCP03 path is:

```bash
cargo run -- test gp_rustlet_security_domain_delegated_scp03 \
  raspi-pico1 --on openocd \
  --serial /dev/cu.usbmodemXXXX:115200 \
  --allow-destructive
```

It rebuilds and reflashes the board. Success ends with:

```text
RUSTLET-SECURITY-DOMAIN-DELEGATED-SCP03-DONE board=raspi-pico1 total=44
```

This scenario and the manual `apdu-tool` path above were both replayed on a
physical Pico1 on 2026-10-15.

## Next Step

Continue with
[Rustlet Security Domain Getting Started](rustlet.security.domain.getting.started.md).
It starts from `simple_security_domain`, adds SCP03 deliberately, and uses the
same Pico1 and client workflow to validate the result.

For exhaustive runtime hooks, policy boundaries, and all protocol profiles,
keep the [Security Domain developer guide](security.domain.developper.guide.md)
as the reference rather than trying to memorize them during this first pass.
