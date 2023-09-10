# Artifact for "Comparse: Provably Secure Formats for Cryptographic Protocols"

## Structure of the repository

- `comparse`: code for all the Comparse framework
- `case_study`: the case studies for Comparse (TLS 1.3, MLS and cTLS)
- `dolev-yao-star`: DY* with Comparse plugged around, and adapted NSL and ISO-DH examples.

## Functions, types, and theorems from the paper

Section 2.1: Formally Defining Message Formats

- [Message format](comparse/src/Comparse.AbstractFormats.fst#L11)
- [Parser](comparse/src/Comparse.AbstractFormats.fst#L22)
- [Serializer](comparse/src/Comparse.AbstractFormats.fst#L35)
- [Induced message format](comparse/src/Comparse.AbstractFormats.fst#L42)

Section 2.2: Properties of Message Formats

- [Non-ambiguity](comparse/src/Comparse.AbstractFormats.fst#L65)
- [Non-ambiguity lemma](comparse/src/Comparse.AbstractFormats.fst#L124)
- [Representation unicity](comparse/src/Comparse.AbstractFormats.fst#L72)
- [Representation unicity lemma](comparse/src/Comparse.AbstractFormats.fst#L141)
- [Non-extensibility](comparse/src/Comparse.AbstractFormats.fst#L168)
- [Non-emptiness](comparse/src/Comparse.AbstractFormats.fst#L160)
- [Non-emptiness lemma](comparse/src/Comparse.AbstractFormats.fst#L247)

Section 3.1: Defining Secure Message Formats in F*

- [Type for secure formats](comparse/src/Comparse.Parser.Builtins.fsti#L16)
- [Type for non-extensible secure formats](comparse/src/Comparse.Parser.Builtins.fsti#L45)
- [Non-emptiness predicate](comparse/src/Comparse.Parser.Builtins.fsti#L140)

Section 3.2: The dependent pair combinator

- [Definition on abstract formats](comparse/src/Comparse.AbstractFormats.fst#L266)
- [Non-ambiguity theorem](comparse/src/Comparse.AbstractFormats.fst#L276)
- [Representation unicity theorem](comparse/src/Comparse.AbstractFormats.fst#L301)
- [Non-extensibility theorem](comparse/src/Comparse.AbstractFormats.fst#L311)
- [Non-emptiness theorem](comparse/src/Comparse.AbstractFormats.fst#L337)
- [F* combinator, non-extensible flavor](comparse/src/Comparse.Parser.Builtins.fsti#L216)
- [F* combinator, extensible flavor](comparse/src/Comparse.Parser.Builtins.fsti#L262)

Section 3.3: The refinement combinator

- [Definition on abstract formats](comparse/src/Comparse.AbstractFormats.fst#L526)
- [Non-ambiguity theorem](comparse/src/Comparse.AbstractFormats.fst#L534)
- [Representation unicity theorem](comparse/src/Comparse.AbstractFormats.fst#L543)
- [Non-extensibility theorem](comparse/src/Comparse.AbstractFormats.fst#L552)
- [Non-emptiness theorem](comparse/src/Comparse.AbstractFormats.fst#L561)
- [RestrictLen non-extensibility theorem](comparse/src/Comparse.AbstractFormats.fst#L580)
- [F* combinator, non-extensible flavor](comparse/src/Comparse.Parser.Builtins.fsti#L409)
- [F* combinator, extensible flavor](comparse/src/Comparse.Parser.Builtins.fsti#L446)
- [F* combinator, RestrictLen](comparse/src/Comparse.Parser.Builtins.fsti#L593)

Section 3.4: The list combinator

- [Definition on abstract formats](comparse/src/Comparse.AbstractFormats.fst#L355)
- [Non-ambiguity theorem](comparse/src/Comparse.AbstractFormats.fst#L412)
- [Representation unicity theorem](comparse/src/Comparse.AbstractFormats.fst#L460)
- [F* combinator](comparse/src/Comparse.Parser.Builtins.fsti#L465)

Section 3.5: The isomorphism combinator

- [Definition on abstract formats](comparse/src/Comparse.AbstractFormats.fst#L474)
- [Non-ambiguity theorem](comparse/src/Comparse.AbstractFormats.fst#L482)
- [Representation unicity theorem](comparse/src/Comparse.AbstractFormats.fst#L492)
- [Non-extensibility theorem](comparse/src/Comparse.AbstractFormats.fst#L502)
- [Non-emptiness theorem](comparse/src/Comparse.AbstractFormats.fst#L512)
- [F* function, non-extensible flavor](comparse/src/Comparse.Parser.Builtins.fsti#L304)
- [F* function, extensible flavor](comparse/src/Comparse.Parser.Builtins.fsti#L364)

Section 3.6: Automating Combinator Synthesis

- [ClientHello F* type](case_study/src/TLS13.MessageFormats.fst#L329)
- [Handshake F* type](case_study/src/TLS13.MessageFormats.fst#L1009)
- [Meta-program entry point](comparse/src/Comparse.Tactic.GenerateParser.fst#L829)

Section 4.1: Format Confusion Attacks in TLS 1.0-1.2

- [Signature for TLS 1.2](case_study/src/TLS13.Signatures.fst#L679)

Section 4.2: Verified Formats for TLS 1.3

- [Handshake format](case_study/src/TLS13.MessageFormats.fst#L1009)
- [Transcript format](case_study/src/TLS13.MessageFormats.fst#L1025)
- [Signatures](case_study/src/TLS13.Signatures.fst#L87)
- [Encryption](case_study/src/TLS13.CryptoInput.fst#L26)
- [Key Derivation](case_study/src/TLS13.CryptoInput.fst#L12)
- [Non-ambiguity with TLS 1.2 signatures](case_study/src/TLS13.Signatures.fst#L695)

Section 4.3: Verified Formats for cTLS

- [cTLS Template](case_study/src/CTLS.Profile.fst#L67)
- [cTLS ClientHello](case_study/src/CTLS.MessageFormats.fst#L556)
- [Compression non-ambiguity](case_study/src/CTLS.Compressions.fst#L23)
- [Compression representation unicity](case_study/src/CTLS.Compressions.fst#L34)
- [Transcript non-ambiguity](case_study/src/CTLS.Transcript.fst#L432)

Section 5.2: Plugging DY∗ and Comparse together

- [Bytes typeclass](comparse/src/Comparse.Bytes.Typeclass.fsti#L22)

Section 5.3: Improving message formats in DY*

- [NSL encryption input](dolev-yao-star/nsl_pk/NSL.Messages.fst#L23)
- [NSL state](dolev-yao-star/nsl_pk/NSL.Sessions.fst#L26)
- [ISO-DH signature](dolev-yao-star/iso-dh/ISODH.Messages.fsti#L22)
- [ISO-DH wire format](dolev-yao-star/iso-dh/ISODH.Messages.fsti#L86)
- [ISO-DH state](dolev-yao-star/iso-dh/ISODH.Sessions.fsti#L28)

## Build

There are three ways to build Comparse.

### Using nix (recommended)

This artifact is reproducible thanks to nix.
It uses the flakes feature, make sure to enable it.

    # This command will compile Z3, F*,
    # and the other dependencies to the correct version
    nix develop

    pushd comparse
    # This command will verify all Comparse
    make
    # This command will run unit tests of Comparse
    make check
    popd

    pushd case_study
    # This command will verify the case studies: TLS 1.3, MLS and cTLS
    make
    popd

    pushd dolev-yao-star
    # Verify the NSL example, modified to use Comparse
    make -C nsl_pk
    # Verify the ISO-DH example, modified to use Comparse
    make -C iso-dh
    popd

### Using docker (recommended)

If nix is not installed on the system, it can be used through a docker image we provide.

    # Build the docker image. This will compile Z3 and F* to the correct version.
    docker build . -t comparse_artifact
    # Start the image and start a shell with correct environment
    docker run -it comparse_artifact

    pushd comparse
    # This command will verify all Comparse
    make
    # This command will run tests of Comparse*, see last section of this README
    make check
    popd

    pushd case_study
    # This command will verify the case studies: TLS 1.3, MLS and cTLS
    make
    popd

    pushd dolev-yao-star
    # Verify the NSL example, modified to use Comparse
    make -C nsl_pk
    # Verify the ISO-DH example, modified to use Comparse
    make -C iso-dh
    popd

### Using a locally-installed F* (not recommended)

This artifact can also be built directly, assuming the host system has the correct dependencies.

This artifact is compatible with:
- F* commit f020d2ac6e7d217d30f85e4361b2eb0b0dde7096
- Z3 version 4.8.5
- OCaml version 4.14

However we can't guarantee everything will go smoothly with this method.

    # Change the PATH to have z3 and fstar.exe
    export PATH=$PATH:/path/to/z3/directory/bin:/path/to/fstar/directory/bin
    # Setup the environment
    export FSTAR_HOME=/path/to/fstar/directory
    eval $(opam env)

    pushd comparse
    # This command will verify all Comparse
    make
    # This command will run tests of Comparse*, see last section of this README
    make check
    popd

    pushd case_study
    # This command will verify the case studies: TLS 1.3, MLS and cTLS
    make
    popd

    pushd dolev-yao-star
    # Verify the NSL example, modified to use Comparse
    make -C nsl_pk
    # Verify the ISO-DH example, modified to use Comparse
    make -C iso-dh
    popd

