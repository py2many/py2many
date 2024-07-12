mkdir -p tests/build
cd tests/build
go mod init github.com/py2many/py2many/tests
go get -u github.com/electrious/refutil
go get -u github.com/hgfischer/go-iter
go get -u github.com/google/go-cmp/cmp

go get github.com/mgechev/revive
if [[ -d /usr/local/bin && ! -f /usr/local/bin/golint && -f $HOME/go/bin/golint ]]; then
  (cd /usr/local/bin && sudo ln -fs $HOME/go/bin/golint)
fi
