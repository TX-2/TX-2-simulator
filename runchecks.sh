#! /bin/sh

base="$(basename $(pwd))"
if ! [ "${base}" = 'TX-2-simulator' ]
then
    exec >&2
    echo 'Please run this script from the top-level directory.'
    exit 1
fi

run_rust_checks_in() {
    if (
        toolchain="${1}"
        subdir="${2}"

        echo "Running Rust ${toolchain} checks in ${subdir}..."
        # We use --no-deps for clippy and when generating
        # documentation because we don't want our CI pipeline to fail
        # just because we depend on a crate with faulty documentation.
        set -x
        cd "${subdir}" &&
            cargo ${toolchain} --locked fmt --all --check &&
            cargo ${toolchain} --locked check  --workspace --all-targets --all-features  --future-incompat-report &&
            cargo ${toolchain} --locked test  --workspace --all-targets --all-features  &&
            cargo ${toolchain} --locked clippy --workspace --all-targets --all-features --no-deps -- -D warnings &&
            cargo ${toolchain} --locked doc --workspace --no-deps
    )
    then
        echo "Rust checks with toolchain ${toolchain} all passed"
    else
        rv="$?"
        echo "Rust checks with toolchain ${toolchain} failed" >&2
        ( exit ${rv} )
    fi
}

rust_checks() {
    here="$(pwd)"
    for toolchain in '+stable' '+nightly'
    do
        for subdir in "${here}" "${here}/tx2-web"
        do
            run_rust_checks_in "${toolchain}" "${subdir}" || return $?
        done
    done
}

npm_checks() {
    (
        # Here we only run 'lint:ts' instead of 'lint' because
        # rust_checks performs the lint checks equivalent to lint:rust
        # (and with more convenient command line option passing).
        cd tx2-web &&
            npm run lint:ts &&
            npm run build -- --locked
    )
}

for check in rust_checks npm_checks
do
    if $check
    then
        printf "%s: OK\n" "${check}"
    else
        rv=$?
        exec >&2
        echo
        echo "check ${check} failed."
        echo
        echo 'Please fix the problems above before committing your change.'
        echo '(if the problem is that wasm-opt was not found, please see docs/build/web.md)'
        exit $rv
    fi
done
echo "Everything is OK"
