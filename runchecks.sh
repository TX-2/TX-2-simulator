#! /bin/sh

base="$(basename $(pwd))"
if ! [ "${base}" = 'TX-2-simulator' ]
then
    exec >&2
    echo 'Please run this script from the top-level directory.'
    exit 1
fi

run_rust_checks_in() {
    (
        echo "Running Rust checks in ${1}..."
        # We use --no-deps for clippy and when generating
        # documentation because we don't want our CI pipeline to fail
        # just because we depend on a crate with faulty documentation.
        cd "$1" &&
            cargo --locked fmt --all --check &&
            cargo --locked test --workspace &&
            cargo --locked clippy --workspace --no-deps -- -D warnings &&
            cargo --locked doc --workspace --no-deps
    )
}

rust_checks() {
    here="$(pwd)"
    for subdir in "${here}" "${here}/tx2-web"
    do
        run_rust_checks_in "${subdir}" || break
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
