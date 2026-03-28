TARGET ?=

.PHONY: run clean

run:
	@test -n "$(TARGET)" || (echo "Usage: make run TARGET=<file>.c" && exit 1)
	infer run --atlas-only -j 1 -- clang -c $(TARGET) > out

debug:
	infer run --atlas-only --debug -j 1 -- clang -c $(TARGET) > out

clean:
	rm -f out
	rm -f *.o
	rm -f *.c.ast.sh
	rm -rf infer-out
