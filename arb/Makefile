.PHONY: build test prove install demo ex2 ex3 ex4 ex6 clean

BIN_DIR := .bin
GO_ENV := CGO_ENABLED=0 GOCACHE=$(CURDIR)/.cache/go-build
ATTORNEY_MODEL_NO_SEARCH := openai://gpt-5
ATTORNEY_MODEL_SEARCH := openai://gpt-5?tools=search

build:
	mkdir -p $(BIN_DIR)
	cd engine && lake build aarengine
	install -m 755 engine/.lake/build/bin/aarengine $(BIN_DIR)/aarengine
	cd runtime && $(GO_ENV) go build -o ../$(BIN_DIR)/aar ./cmd/aar

test:
	cd runtime && $(GO_ENV) go test ./...

prove:
	cd engine && lake build Proofs

install: build

demo: build
	rm -rf out/ex1-demo
	examples/ex1/sign.sh
	.bin/aar complain --situation examples/ex1/situation.md --out examples/ex1/complaint.md
	.bin/aar case --complaint examples/ex1/complaint.md --out-dir out/ex1-demo --attorney-model $(ATTORNEY_MODEL_NO_SEARCH)

ex2: build
	rm -rf out/ex2-demo
	.bin/aar complain --situation examples/ex2/situation.md --out examples/ex2/complaint.md
	.bin/aar case --complaint examples/ex2/complaint.md --out-dir out/ex2-demo --attorney-model $(ATTORNEY_MODEL_NO_SEARCH)

ex3: build
	rm -rf out/ex3-demo
	.bin/aar complain --situation examples/ex3/situation.md --out examples/ex3/complaint.md
	.bin/aar case --complaint examples/ex3/complaint.md --out-dir out/ex3-demo --attorney-model $(ATTORNEY_MODEL_NO_SEARCH)

ex4: build
	rm -rf out/ex4-demo
	.bin/aar case --complaint examples/ex4/complaint.md --out-dir out/ex4-demo --attorney-model $(ATTORNEY_MODEL_SEARCH)

ex6: build
	rm -rf out/ex6-demo
	.bin/aar case --complaint examples/ex6/complaint.md --out-dir out/ex6-demo --attorney-model $(ATTORNEY_MODEL_SEARCH)

clean:
	rm -rf $(BIN_DIR) engine/.lake/build out/ex1-demo out/ex2-demo out/ex3-demo out/ex4-demo out/ex6-demo
