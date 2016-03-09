default : Cell.class SimpleCell CounterCell Parrot SelfRefExample

% : %.class
	@echo "======================================================================"
	@echo "$*"
	@echo "======================================================================"
	@java $* Hello world

%.class : %.java
	javac $<

# EOF
