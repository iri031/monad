set -e
brew install --cask emacs
brew install opam swi-prolog cairo expat gtk+3 gtksourceview3 libffi libxml2 zlib llvm cmake pkg-config coreutils
opam init --yes --shell-setup
eval $(opam env)
echo "" >> ~/.zshrc
echo "source ~/.profile" >> ~/.zshrc # opam init writes to ~/.profile
#export PATH="/opt/homebrew/opt/llvm/bin:$PATH"
#export LDFLAGS="-L/opt/homebrew/opt/llvm/lib"
