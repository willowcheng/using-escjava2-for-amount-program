public class Amount{

 private int cents;

 private int dollars;

 public Amount(int dollars, int cents){
   this.dollars = dollars;
   this.cents = cents;
 }

 public Amount negate(){
   return new Amount(-cents, -dollars);
 }

 public Amount subtract(Amount a){
   return this.add(a.negate());
 }

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
