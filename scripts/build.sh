#!/bin/bash

EUSOLVER_ROOT=`pwd`

# --------------------------------------

# Change to yes and set Z3_PYTHON_PATH to where z3 python module exists,
# or leave it blank if z3 modules exist in the standard python3 path
HAVE_Z3=yes

# Z3_PYTHON_PATH=$LOCAL_Z3_ROOT/thirdparty/z3/build/python
REBUILD_LOCAL_Z3=no

# --------------------------------------

# TODO: Check for existence of cmake, python3, pyparsing etc

LOCAL_Z3_ROOT="$EUSOLVER_ROOT"/thirdparty/z3

# Build libeusolver
pushd "$EUSOLVER_ROOT"/thirdparty/libeusolver/build
cmake ..
make
LIBEUSOLVER_PYTHON_PATH="$EUSOLVER_ROOT"/thirdparty/libeusolver/build
popd

# Build z3
if [ x"$HAVE_Z3" = "xno" ]; then
	echo "Using local copy of z3..."
	echo "Checking if z3 is already built..." 
	if [ -e "$LOCAL_Z3_ROOT"/build/libz3.so ] && [ -e "$LOCAL_Z3_ROOT"/build/python/z3 ]; then
		echo "Z3 already built. Not rebuilding..."
		echo "Set REBUILD_LOCAL_Z3 to yes to rebuild anyway..."
	else
		pushd "$LOCAL_Z3_ROOT"
		python scripts/mk_make.py
		cd build
		make
		popd
	fi
	Z3_PYTHON_PATH="$EUSOLVER_ROOT"/thirdparty/z3/build/python
else
	echo "Using provided z3 paths"
	if python3 -c "import sys; sys.path.append('"$Z3_PYTHON_PATH"'); import z3"; then
		echo "Found z3 python bits"
	else
		echo "Did not find z3 python bits or z3 python bits can't find libz3.so..."
		exit 1
	fi
fi

# Check for existence of pyparsing
if python3 -c "import pyparsing"; then
	echo "Found pyparsing"
else
	echo "Did not find pyparsing; Attempting to install using pip3"
	pip3 install pyparsing
	if [ $? -eq 0 ]; then
		echo "pyparsing installed successfully..."
	else
		echo "[ERROR] Cannot install pyparsing"
		exit 1
	fi
fi
cd $EUSOLVER_ROOT

EXEC_SCRIPT="
#!/bin/bash

PYTHONPATH=$Z3_PYTHON_PATH:$LIBEUSOLVER_PYTHON_PATH:"'$PYTHONPATH'" python3 src/benchmarks.py "'$@'"

# EOF
"
echo "Writing executable script..."
cat > eusolver <<< "$EXEC_SCRIPT"
chmod +x eusolver
