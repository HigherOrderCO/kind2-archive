build:
	cd book; \
		kind2 to-js main > main.js

check:
	cd book; \
		kind2 check main