#!/bin/bash

set -e
set -u

ORIGDIR=`pwd`
STAREXECDIR=starexec_upload
TAR_FILE="$STAREXECDIR".tar.gz
TEMPDIR="$STAREXECDIR"/temp
GIT_REPO=git@bitbucket.org:abhishekudupa/eusolver.git 
PYTHONURL=https://www.python.org/ftp/python/3.5.1/Python-3.5.1.tgz
TESTBENCHMARK=benchmarks/icfp/icfp_103_10.sl 

echo "Removing any existing directory $STAREXECDIR" && rm -rf "$STAREXECDIR"
echo "Creating directory structure for $STAREXECDIR" && mkdir -p "$STAREXECDIR/"{bin,thirdparty}

mkdir -p "$TEMPDIR"
echo "Cloning repo git@bitbucket.org:abhishekudupa/eusolver.git" && git clone -q --recursive "$GIT_REPO" "$TEMPDIR" 2>/dev/null

cp -R "$TEMPDIR"/thirdparty/libeusolver "$STAREXECDIR"/thirdparty/
cp -R "$TEMPDIR"/thirdparty/z3 "$STAREXECDIR"/thirdparty/

# Make eusolver stuff use old version of tools on starexec 
echo "Rewriting build scripts in libeusolver to use older tool versions from Starexec"
sed -i 's/3.2.0/2.8.11/' "$STAREXECDIR"/thirdparty/libeusolver/CMakeLists.txt
sed -i 's/c++14/c++11/' "$STAREXECDIR"/thirdparty/libeusolver/CMakeLists.txt
sed -i '/COMMAND python3/d' "$STAREXECDIR"/thirdparty/libeusolver/CMakeLists.txt

rm -rf "$TEMPDIR"

# Download python
echo "Getting Python-3.5.1" && wget --quiet -O "$STAREXECDIR"/thirdparty/Python-3.5.1.tgz "$PYTHONURL"

# Copy sources to bin directory
echo "Copying sources into $STAREXECDIR/bin" && cp -R src/* "$STAREXECDIR"/bin/

# Where is pyparsing installed
PIP_OUTPUT=`pip3 show -f pyparsing`
PYPARSING_LOCATION=`sed -n 's/Location: *//p' <<< "$PIP_OUTPUT"`

if [ -e "$PYPARSING_LOCATION"/pyparsing.py ]; then
	echo "Copying pyparsing.py from $PYPARSING_LOCATION to $STAREXECDIR/bin"
	cp "$PYPARSING_LOCATION"/pyparsing.py "$STAREXECDIR"/bin
else
	echo "Could not find pyparsing.py"
fi

echo "Copying test benchmark" && cp "$TESTBENCHMARK" "$STAREXECDIR"/bin

cat > $STAREXECDIR/starexec_build << EOF

#!/bin/bash

cd thirdparty

# Build libeusolver
cd libeusolver/build && cmake ..
make && cd ..
cd ..

# Build python3
tar -xf Python-3.5.1.tgz
cd Python-3.5.1 && ./configure && make && cp python python3 && cd ..

# Build z3
cd z3
python scripts/mk_make.py
cd build && make && cd ..
cd ..

cd ..

cd bin && ./starexec_run_default `basename "$TESTBENCHMARK"`

EOF

cat > "$STAREXECDIR"/bin/starexec_run_default << "EOF"
#!/bin/bash

PYPATH="../thirdparty/Python-3.5.1/python"
WORKDIR=`pwd`
export Z3_LIBRARY_PATH="$WORKDIR/../thirdparty/z3/build/python"

if [ -z "$PYPATH" ]; then
	echo "python3 not found"
else
	sed -i 's/^import pkg_resources/# &/' ../thirdparty/z3/build/python/z3/z3core.py
	sed -i 's!^\(\s*\)_dirs =.*$!\1_dirs = ["'$Z3_LIBRARY_PATH'"]!' ../thirdparty/z3/build/python/z3/z3core.py
	PYTHONPATH=../thirdparty/libeusolver/build:../thirdparty/z3/build/python "$PYPATH" benchmarks.py "$1"
fi

EOF

cat > "$STAREXECDIR"/starexec_description.txt << EOF
Solver combining enumerative and unification synthesis strategies
EOF

chmod +x "$STAREXECDIR"/bin/starexec_run_default
chmod +x "$STAREXECDIR"/starexec_build


echo "Tarring $STAREXECDIR" && cd "$STAREXECDIR" && tar -zcf ../"$TAR_FILE" . && cd ..
echo "Removing $STAREXECDIR" && rm -r "$STAREXECDIR"

