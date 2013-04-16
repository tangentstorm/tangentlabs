ANTLR4 = java -jar ~/jar/antlr-4.0-complete.jar
GRUN   = java org.antlr.v4.runtime.misc.TestRig
hello:
	$(ANTLR4) Hello.g4
	javac Hello*.java
	echo "hello world" | $(GRUN) Hello r -tree
