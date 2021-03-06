#!/bin/bash

COQ_BUILD_DIR="coq-$COQ_VER"

if [ "$COQ_VER" == "" ]
then
    echo "Environment does not contain a setting for COQ_VER. Please set it up" 1>&2
    exit 1;
fi


function setopamenv ()
{
    eval `opam config env --root="$COQ_BUILD_DIR"`
}

function init()
{
    mkdir -p "coq-$COQ_VER"
    opam init --root="$COQ_BUILD_DIR" --no-setup --yes
    setopamenv
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam pin add coq "$COQ_VER" --yes
    opam install coq-bignums --yes
    opam list
    # opam install "coq.$COQ_VER" --yes
}

function configure()
{
    setopamenv
    ./configure.sh
}

function build()
{

    configure
    coqtop -v
    make
}

function html()
{
    configure
    make html
}

function install()
{
    build
    make install
}

function clean()
{
    make clean
}

function usage()
{

cat <<EOF
Usage : COQ_VER=[VERSION_OF_COQ] $0 [COMMAND]
The set of allowed commands are

  * init      - install necessary packages in an appropriate root.
  * configure - get ready to make the project
  * build     - build the project
  * html      - build the html documentation
  * install   - install the package in the current opam environment.
  * clean
EOF

}

case $1 in
    init) init; ;;
    configure) configure; ;;
    build) build; ;;
    html) html; ;;
    install) install; ;;
    clean) clean; ;;
    help) usage; ;;
    *) echo "$0:error:" unknown command "$1" ; usage ; ;;
esac
