public class SelfRefExample {

    public void m1() {
	System.out.println("m1 called");
	m2(); // self ref call
    }

    public void m2() {
	System.out.println("m2 called");
    }
 
    public static void main(String[] args) {
	SelfRefExample ex = new SelfRefExample();
	ex.m1();
    }
}
