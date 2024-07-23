build:
	cd book; \
		cargo run -- to-js main > main.js

check:
	cd book; \
		kind2 check main