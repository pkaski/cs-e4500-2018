
import collection.mutable.ArrayBuffer

/* 
 * An abstract base trait for elements of a ring.
 *
 * (We tacitly assume that rings are commutative and 0 != 1.) 
 *
 */

trait Ring[E <: Ring[E]] {

  /* Operations that must be implemented in an extending class. */

  def zero: E           // returns the additive identity element
  def one: E            // returns the multiplicative identity element
  def unary_-(): E      // additive inverse of this
  def +(that: E): E     // sum of this and that
  def -(that: E): E     // difference of this and that
  def *(that: E): E     // product of this and that
  def isUnit: Boolean   // this element is a unit?
  def inverse: E        // multiplicative inverse of this
                        // (should fail if this is not a unit)

  /* Extending classes implement quotient and remainder algorithms,
   * if available for the type of ring -- by default not available. */

  def quotient(that: E): E  = { assert(false); that }
  def remainder(that: E): E = { assert(false); that }

  /* Generic operations relying on the above ring-type-specific operations. */

  def /(that: E): E = this*that.inverse

  def extgcd(that: E): (Int,    // l -- index for the gcd in the sequences
                        Seq[E], // r -- remainder sequence
                        Seq[E], // s -- Bezout coefficients of "this"
                        Seq[E], // t -- Bezout coefficients of "that"
                        Seq[E]  // q -- quotient sequence
                       ) = {
    val r = ArrayBuffer[E](this.asInstanceOf[E], that)
    val s = ArrayBuffer(one,  zero)
    val t = ArrayBuffer(zero, one)
    val q = ArrayBuffer(zero)
    var i = 1
    while(r(i) != zero) {
      q.append( r(i-1) quotient r(i) )
      r.append( r(i-1) - q(i)*r(i) )
      s.append( s(i-1) - q(i)*s(i) )
      t.append( t(i-1) - q(i)*t(i) )
      i = i + 1
    }
    val l = i - 1
    (l, r.toSeq, s.toSeq, t.toSeq, q.toSeq)
  }

  def gcd(that: E) = { 
    val (l,r,s,t,q) = this extgcd that
    r(l)
  }

  def lcm(that: E) = (this*that) quotient (this gcd that)

  def divides(that: E) = (this remainder that) == zero
}




/* 
 * The ring of integers Z, implemented by relying on Scala's library BigInt.
 *
 * Observe how we extend the parameterized base trait Ring[ ] to get the
 * generic operations. Observe also that the constructor is private by
 * convention, i.e. ring elements should be constructed using the 
 * companion object.
 * 
 */

class Z private (val v: BigInt) extends Ring[Z] {
  override def toString = v.toString

  def zero                        = Z(0)
  def one                         = Z(1)
  def unary_-()                   = Z(-this.v)
  def +(that: Z)                  = Z(this.v + that.v)
  def -(that: Z)                  = Z(this.v - that.v)
  def *(that: Z)                  = Z(this.v * that.v)
  def isUnit                      = this.v.abs == 1
  def inverse                     = { assert(isUnit); this }
  override def quotient(that: Z)  = Z((this.v - (this.v mod that.v))/that.v)
  override def remainder(that: Z) = Z(this.v mod that.v)

  override def hashCode = this.v.hashCode
  override def equals(other: Any) = other match {
    case that: Z => this.v == that.v
    case _       => false
  }
}

object Z {
  def apply(v: BigInt) = new Z(v)
}



/* 
 * A quotient ring modulo a modulus that assumes the ring E supports 
 * quotient and remainder.
 *
 */

class QuotientRing[E <: Ring[E]] private (modulus: E) {
  def zeroE = modulus.zero
  def oneE  = modulus.one
  class Q(val v: E) extends Ring[Q] { 
    override def toString = v.toString
//    override def toString = v.toString + " mod " + modulus.toString

    def zero         = Q(zeroE)
    def one          = Q(oneE)
    def unary_-()    = Q(-this.v)
    def +(that: Q)   = Q((this.v + that.v) remainder modulus)
    def -(that: Q)   = Q((this.v - that.v) remainder modulus)
    def *(that: Q)   = Q((this.v * that.v) remainder modulus)
    def isUnit       = (this.v gcd modulus) == oneE
    def inverse      = { val (l,r,s,t,q) = this.v extgcd modulus
                         assert(r(l) == oneE)
                         Q(s(l) remainder modulus) }

    override def hashCode = v.hashCode + modulus.hashCode
    override def equals(other: Any) = other match {
      case that: Q => this.v == that.v
      case _       => false
    }
  }
  object Q {
    def apply(v: E) = new Q(v)
  }

  def apply(v: E) = Q(v)
}

object QuotientRing {
  def apply[E <: Ring[E]](modulus: E) = new QuotientRing(modulus)
}



/* 
 * A rational ring that assumes the ring E supports quotient and remainder.
 * The constructor needs an arbitrary element s to gain access to E. 
 *
 */

class RationalRing[E <: Ring[E]] private (val s: E) {
  def zeroE = s.zero
  def oneE  = s.one
  class Q private (val p: E, val q: E) extends Ring[Q] { 
    override def toString = 
      if(q == oneE) p.toString else (p.toString + " / " + q.toString)

    def zero         = Q(zeroE, oneE)
    def one          = Q(oneE,  oneE)
    def unary_-()    = Q(-this.p, this.q)
    def +(that: Q)   = Q(this.p*that.q + that.p*this.q, this.q*that.q)
    def -(that: Q)   = Q(this.p*that.q - that.p*this.q, this.q*that.q)
    def *(that: Q)   = Q(this.p*that.p, this.q*that.q)
    def isUnit       = this.p != zeroE
    def inverse      = { assert(isUnit); Q(this.q, this.p) }

    override def hashCode = p.hashCode + q.hashCode
    override def equals(other: Any) = other match {
      case that: Q => (this.p == that.p) && (this.q == that.q)
      case _       => false
    }
  }
  object Q {
    def apply(p: E, q: E) = { 
      assert(q != zeroE)
      new Q(p quotient (p gcd q), q quotient (p gcd q)) 
    }
  }

  def apply(p: E, q: E) = Q(p,q)
}

object RationalRing {
  def apply[E <: Ring[E]](s: E) = new RationalRing(s)
}




/*
 * A univariate polynomial ring with coefficients in R.
 * The constructor needs an arbitrary element s to gain access to R.
 *
 */ 

class PolynomialRing[R <: Ring[R]] private (val s: R, val indet: String = "x") {
  def zeroR = s.zero
  def oneR  = s.one
  class P private (val a: Seq[R]) extends Ring[P] {

    def degree  = a.length - 1
    def lc      = if(degree < 0) zeroR else a(degree)
    def isMonic = lc == oneR

    def apply(i: Int) = { assert(i >= 0 && i <= degree); a(i) }
    def apply(v: R) = a.dropRight(1)
                       .foldRight(lc)((x,y) => v*y+x)
    def shift(j: Int) = { assert(j >= 0); P((0 until j).map(i=>zeroR) ++ a) }

    override def toString = {
      if(a.isEmpty) {
        "(" + zeroR.toString + ")"
      } else {
        a.zipWithIndex
         .filter(x => x._1 != zeroR)
         .map(x => { var s = "(" ++ x._1.toString ++ ")" 
                     val d = x._2
                     if(d == 1) { s = s ++ indet }
                     if(d>=2 && d<=9) { s = s ++ indet ++ "^" ++ d.toString }
                     if(d >= 10) { s = s ++ indet ++ "^{" ++ d.toString ++ "}" }
                     s })
         .reduce(_ ++ " + " ++ _)
      }
    }

    def zero = P(Seq[R]())
    def one  = P(Seq(oneR))
    def unary_-() = P(this.a.map(-_))
    def +(that: P) = P(P.zipZero(this.a,that.a).map(x => x._1 + x._2))
    def -(that: P) = P(P.zipZero(this.a,that.a).map(x => x._1 - x._2))
    def *(that: R) = P(this.a.map(_*that))
    def *(that: P) = P((0 to (this.degree + that.degree + 1)).map(
                       i => ((0 max (i - that.degree)) to (i min this.degree))
                              .foldLeft(zeroR)((t,j) => t + this(j)*that(i-j))))
    def isUnit = this.degree == 1 && this.lc.isUnit
    def inverse = { assert(this.isUnit); P(Seq(this.lc.inverse)) }
    override def quotient(that: P) = {
      val mu = that.lc.inverse
      var r = P(this.a)
      var i = this.degree - that.degree
      val q = (0 to i).map(x => zeroR).toBuffer
      while(i >= 0) {
        if(r.degree == that.degree + i) {
          q(i) = r.lc*mu
          r = r - that.shift(i)*q(i)
        } 
        i = i - 1
      }
      P(q)
    } 
    override def remainder(that: P) = this - (this quotient that)*that

    override def hashCode = a.map(_.hashCode).sum
    override def equals(other: Any) = other match {
      case that: P => P.zipZero(this.a,that.a).forall(x => x._1 == x._2)
      case _       => false
    }
  }

  object P {
    def trim(a: Seq[R]) = a.take((a.zipWithIndex.filter(x => x._1 != zeroR)
                                                .map(_._2) :+ -1).max + 1)
    def zipZero(a: Seq[R], b: Seq[R]) = trim(a).zipAll(trim(b), zeroR, zeroR)
    def x(j: Int) = { assert(j >= 0); 
                      P((0 to j).map(i => if(j == i) oneR else zeroR)) }
    def apply(a: Seq[R]) = new P(trim(a))
  }
  def apply(a: Seq[R]) = P(a)
}

object PolynomialRing {
  def apply[R <: Ring[R]](s: R, indet: String = "x") = 
    new PolynomialRing(s, indet)
}

