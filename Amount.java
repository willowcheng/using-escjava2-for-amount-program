public class Amount{

 private int cents;
//@ invariant Math.abs(cents) < 100;
 private int dollars;
//@ requires Math.abs(cents) < 100;
 public Amount(int dollars, int cents){
   this.dollars = dollars;
   this.cents = cents;
 }
//@ ensures \result != null;
 public Amount negate(){
   return new Amount(-this.dollars, -this.cents);
 }
 //@ requires a != null;
 public Amount subtract(Amount a){
   return this.add(a.negate());
 }
//@ requires a != null;
 public Amount add(Amount a){
   int new_dollars = dollars + a.dollars;
   int new_cents = cents + a.cents;
   if (new_cents < -100) {
      new_cents = new_cents + 100;
      new_dollars = new_dollars - 1;
   }
   if (new_cents > 100) {
      new_cents = new_cents - 100;
      new_dollars = new_dollars - 1;
   }
   if (new_cents < 0 && new_dollars > 0) {
       new_cents = new_cents + 100;
       new_dollars = new_dollars - 1;
   }
   if (new_cents >= 0 && new_dollars <= 0) {
       new_cents = new_cents - 100;
       new_dollars = new_dollars + 1;
   }
   return new Amount(new_dollars,new_cents);
 }

 public boolean equal(Amount a) {
   if (a==null) return false;
   else return (dollars == a.dollars && cents == a.cents);
 }

}
