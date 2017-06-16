all:
	$(MAKE) -C src all
clean:
	$(MAKE) -C src clean
	rm *.*~

clean_parser:
	$(MAKE) -C src clean_parser



