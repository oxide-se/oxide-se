include dependencies.mk

%.vo: %.v
	$(COQC) $(FLAGS) $<
