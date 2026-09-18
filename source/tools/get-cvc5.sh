#! /bin/bash -eu

cvc5_version="1.3.4"

if [ `uname` == "Darwin" ]; then
    if [[ $(uname -m) == 'arm64' ]]; then
        filename="cvc5-macOS-arm64-static"
    else
        filename="cvc5-macOS-x86_64-static"
    fi
elif [ `uname` == "Linux" ]; then
    if [[ $(uname -m) == 'aarch64' ]]; then
        filename="cvc5-Linux-arm64-static"
    else
        filename="cvc5-Linux-x86_64-static"
    fi
elif [[ $(uname) == "MINGW64_NT"* ]]; then
    filename="cvc5-Win64-x86_64-static"
fi

URL="https://github.com/cvc5/cvc5/releases/download/cvc5-$cvc5_version/$filename.zip"

echo "Downloading: $URL"
curl -L -o "$filename.zip" "$URL"
unzip "$filename.zip"

# On Windows the binary is cvc5.exe; elsewhere it is cvc5.
if [[ $(uname) == "MINGW64_NT"* ]]; then
    # delete the existing cvc5 because of caching issue
    rm -f cvc5.exe
    cp "$filename/bin/cvc5.exe" .
else
    # delete the existing cvc5 because of caching issue on macs
    rm -f cvc5
    cp "$filename/bin/cvc5" .
fi
echo "cvc5 located at $(pwd)"
rm -r "$filename"
rm "$filename.zip"
