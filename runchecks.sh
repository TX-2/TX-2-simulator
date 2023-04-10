#! /bin/sh

base="$(basename $(pwd))"
if ! [ "${base}" = 'TX-2-simulator' ]
then
    exec >&2
    echo 'Please run this script from the top-level directory.'
    exit 1
fi

rust_checks() {
    cargo fmt --check &&
        cargo test &&
        cargo clippy
}

npm_checks() {
    (
        cd tx2-web &&
            npm run lint &&
            npm run build
    )
}

if rust_checks && npm_checks
then
    echo "Everything is OK"
else
    rv=$?
    exec >&2
    echo
    echo 'Please fix the problems above before committing your change.'
    echo '(if the problem is that wasm-opt was not found, please see docs/build/web.md)'
    exit $rv
fi
