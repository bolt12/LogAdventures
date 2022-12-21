# LogAdventures (**WORK IN PROGRESS**)

```agda
module README where
```

This is a literate Agda file, all code written here type
checks. Github's LateX support is also used write equational reasoning
proofs in a similar way one would do in Agda and Agda's lemma names
one might be familiar were favored, except when there was no suitable
lemma yet or when the reasoning is rather trivial.

## Context

Recently I found myself needing to write a proof involving logarithms
on natural numbers in Agda. I came to realise that at the time Agda
didn't have any out of the box support for logarithms (of base 2) so I
gave it a go (see
[here](https://github.com/agda/agda-stdlib/pull/1782)). I managed to
write a truncated versions of $\log$ in Agda and successfully proved
what I wanted.

I quickly realised that my truncated $\log$ is only so useful, and
does not allow one to prove more interesting things using the known
logarithmic identity properties. Since it is not written as the
composition of two other more fundamental functions it loses
information. For instance, the floored logarithm:
$\lfloor \log_2 \rfloor = \lfloor \textunderscore \rfloor \circ \log_2$,
where $\log_2$ computes the exact value of the logarithm and
$\lfloor \textunderscore \rfloor$ floors the result to the nearest
smallest integer.

Division on natural numbers is similar in this sense, but we can
recover lost information, i.e. make integer division bijective by
computing its remainder (hence obtaining the known `divMod` function),
and relate it with its quotient via the following theorem:
$dividend = divisor * quotient + remainder$ called Quotient
Remainder Theorem (QRT).

Unfortunately, information loss interferes with compositionality.
Division on naturals is about lowering resolution and the `mod`
function captures exaclty the information that division discards. So,
in the same way that `divMod` is bijective and so fixes the
information loss of `div`, is there a neat, bijective augmentation of
$\lfloor \log_2 \rfloor = \lfloor \textunderscore \rfloor \circ \log_2$
(assuming positive integers as arguments, at least for now), and what
would be the theorem that relates everything together?

## Finding a way to recover the lost information

There's not much literature on this particular topic. Most ways to
compute logarithm involve dividing the argument by some factor
(usually involves the base of the logarithm) multiple times. If
integer division is used one gets a truncated result, if floating
point division is used we get an approximate result. Interestingly,
there's no known algorithm that can compute an exact result using
`divMod`, and even if one could exist what would be the relationship
between the "remainder" (I overload the word "remainder" to mean a
remainder like notion, usually a fractional part, which relates with
the integer part according to some specification) and the integer part
of such result? Let's think about this one first.

The fractional part of a $\log_2$ computation behaves
logarithmically. This is can be highlighted by the following
logarithmic identity:
$\log_b (x * \frac{1}{x}) = \log_b x + \log_b \frac{1}{x}$. Given
this, it's difficult to imagine how a specification for it that does
not mentions logarithms could look. Attempts started by drawing
inspiration from the division's specification (QRT), where the quotient is
applied to the inverse function (multiplication) and the remainder is
an additive one. Following this, $\log$'s inverse is the
exponentiation function so it looks something of the form:
$\log_b a = (x, r) \implies a = b^x + r$, assuming here that our
logarithm function returns both integer and remainder parts. A reader
with a good deal of experience with logarithmic functions and their
properties will see addition ( $b^x + r$ ) in the argument to $\log_b$
as slightly suspicious, due to the fact that there are no known simple
properties which involve $\log$ of sums. This path will lead to many
obstacles exactly because of this. Alternatively, one should pursue a
path where there are useful properties to leverage from and there are
a lot for multiplication or division!

Multiplication [is
often](https://repositorio.inesctec.pt/server/api/core/bitstreams/844cf125-abaf-447c-aecf-fa8fe3ff47e1/content)
regarded as much simpler than its dual/inverse: division. In the same
spirit, the dual/inverse of the logarithm, i.e. exponentiation, is
also deemed simpler since both build on top of the same
operations. Having said this, it is helpful to reason and explore on
the easy side and once finished go back to the dual side, since the
specification that relates the $\log$ computation remainder and
integer results must be also related via exponentiation.

Getting the integer part of the result is not difficult, even in
computational terms it is known how to get the truncated results as I
mentioned in the first section. However, recovering the lost
information by the truncation and relate it with the argument and
result is what we are after.

Let's start with a manual example, and try figuring out how we can
find and relate the remainder of a particular logarithmic
computation. $\log_2 20 \approx 4.321$ so $4$ is integer part and
$0.321$ is the fractional part. As mentioned earlier, if the theorem
that relates these two values were to be such that the remainder was
additive, then it would be as simple as making the remainder be the
fractional part $0.321$, however, as also mentioned previously, doing
so would not be much of interest since one wouldn't be able to relate
it to other logarithmic properties. What we try instead is to find how
such additive remainder can look like on the dual (simpler) operation
side $x = \log_2 20 \iff 2^x = 20$, if we make $x = (i + r)$
( $integer + remainder$ ) then
$(i + r) = \log_2 20 \iff 2^{i + r} = 20$. We know that, for this
example, $i = 4$, so $2^{4 + r} = 20$. Notice how this is equivalent
to finding a way to decompose $20$ into two powers of two parts on the
(dual-dual) logarithm side:
$20 = 2^i * 2^r \implies \log_2 20 = \log_2 (2^i * 2^r) = \log_2 2^i + \log_2 2^r = i + r$
this reasoning is arguably more contrived.

Solving the previous equation for $r$ gives us
$2^r = 20 / 2^4 = 20 / 16 ≡ 5 / 4$, this means that by applying the
inverse relation again we get $r = \log_2 (5 / 4)$, and thus the
remainder is found! And just to double check, $\log_2 (5 / 4)$ is
around $0.321$ (i.e. the fractional part of $\log_2 20$). So if
$i = 4$ and $r = \log_2 (5/4)$, one gets:

$$
\begin{align*}
 & 2^{4 + \log_2 (5 / 4)} \\
=&\langle\ {\textasciicircum}\text{\{ - \}}{distrib^l}\text{\{ -+-* \}} 2\ 4\ (5 / 4)\ \rangle \\
 & 2^4 * 2^{\log_2 (5 / 4)} \\
=&\langle\ cong\ (\lambda x \rightarrow 2^4 * x)\ 2^{\log_2 x} {\equiv} x\ \rangle\\
 & 2^4 * (5 / 4) \\
=&\langle\ \text{\{ trivial \}}\ \rangle \\
 & 16 * (5 / 4) \\
=&\langle\ \text{\{ trivial \}}\ \rangle \\
 & 20
\end{align*}
$$

Since the remainder is a logarithm exponent, it can be simplified to be
just the argument to the logarithm, via the logarithmic identity
$\log_b b^a \equiv a$. So if we have something like `divMod` but for
$\log$ where $\log\ b\ a = (x , y)$, where $x$ is the integer part and
$y$ is the simplified remainder, then this is the specification that
ties everything together:

$$
log\ b\ a \equiv (x , y) \implies a \equiv b^x * y
$$

A multiplicative rather than additive remainder in the logarithmic
realm, relating to an additive remainder in the exponent realm!
Substituting $a$ with the left hand part we get:

$$
\begin{align*}
 & \log_2 (2^x * y) \\
=&\langle\ \log_2 [ a * b ]{\equiv}\log_2 a {+} \log_2 b\ \ 2^x\ \ y\ \rangle \\
 & \log_2\ 2^x + \log_2 y \\
=&\langle\ \text{\{ trivial \}}\ \rangle\\
 & x + \log_2 y \\
\end{align*}
$$

And, as stated in the beginning, we recover the exact equation that
one was naively attempting to pursue, except that we now have much
more profound insights into the relationship of all these variables.

Notice that just like the QRT doesn't tell us much how to actually
compute division, but only asserts that division result is correct,
the logarithm theorem uncovered above also only allows one to assert
that logarithm result is correct.

## Why is the remainder rational?

Notice the following resemblance between the QRT and the theorem
uncovered for logarithms:

Let $divMod\ a\ b = (div\ a\ b , mod\ a\ b) = (x , y)$ then we have
$x * b + y = a$. Let
$logMod_b\ a = (\log_b a, \log {\textunderscore} mod_b\ a) = (x, y)$
then we have $b^x * y = a$. These two seem very similar, the only odd
thing is that $y$ has to be rational, not integer. For the integer
result part, one applies the inverse function (multiplication for
division and exponentiation for logarithm), for the
fractional/remainder part the remainder is added in the `divMod` case,
but multiplied in the $\log$ case. The key insight here is to see that
in the $\log$ case one is actually adding the remainder as well, but
in an exponential position and that translates to multiplication. And,
actually for division the remainder is only an integer if their
arguments are integer numbers as well. If we apply exactly the same
reasoning as in the previous section: division is the inverse of
multiplication via $a / b = x \iff x * b = a$; let $x$ be the sum of
an integer part ( $i$ ) with a fractional part ( $r$ ) $i + r$ then,
substituting $x$ one gets

$$
\begin{align*}
 & (i + r) * b = a \\
=&\langle\ \ast\text{\{ - \}}{distrib^r}\text{\{ -+ \}}\ b\ x\ y\ \rangle\\
 & i * b + r * b = a \\
\end{align*}
$$

This is very close to the `divMod` theorem (QRT) that relates quotient
and remainder for integer numbers, the insight comes by the fact (or
coincidence) That $r * b$ is always a integer number. So for integer
number division the formula can be simplified to $i * b + r$. Proof
that $r * b$ is always integer: Given that
$a * i + b * r = a \iff b * r = a - a * r$ and since $a$ and $a * i$
are naturals and naturals are closed under subtraction, $r * b$ is an
integer.

## Does $\log_2 (a * b) = \log_2 a + \log_2 b$ hold?

Assume $\log_2 a = (x_1 , y_1)$ and $\log_2 b = (x_2 , y_2)$ and that
$x_1, y_1$ and $x_2, y_2$ are related by the theorem uncovered on the
previous sections:

$$
\begin{align*}
 & \log_2 (a * b) \\
=&\langle\ \text{\{ apply \}} b^x * y = a\ \rangle\\
 & \log_2 ((2^{x_1} * y_1) * (2^{x_2} * y_2)) \\
=&\langle\ \text{\{ note that \}} y = 2^{\log_2 y}\ \rangle \\
 & \log_2 (2^{x_1 + \log_2 y_1} * 2^{x_2 + \log_2 y_2}) \\
=&\langle\ sym\ (cong\ \log_2 ({\textasciicircum}\text{\{ - \}}{distrib^l}\text{\{ -+-* \}}\ 2\ (x_1 + \log_2 y_1)\ (x_2 + \log_2 y_2))\ \rangle\\
 & log₂ (2^{x_1 + \log_2 y_1 + x_2 + \log_2 y_2}) \\
=&\langle\ \log_2 [ 2ˣ ]{\equiv}x\ \rangle \\
 & x_1 + \log_2 y_1 + x_2 + \log_2 y_2 \\
=&\langle\ \text{\{ trivial \}}\ \rangle \\
 & x_1 + x_2 + \log_2 y_1 + \log_2 y_2 \\
=&\langle\ cong\ (\lambda x \rightarrow x_1 + x_2 + x) (\log_2 [ a * b ]{\equiv}\log_2 a {+} \log_2 b\ \ y_1\ y_2)\ \rangle \\
 & x_1 + x_2 + \log_2 (y_1 * y_2) \\
=&\langle\ cong\ (\lambda x \rightarrow x_1 + x_2 + x) (\log_2 [ a * b ]{\equiv}\log_2 a {+} \log_2 b\ \ y_1\ y_2)\ \rangle \\
 & x_1 + x_2 + \log_2 y_1 + \log_2 y_2 \\
=&\langle\ \text{\{ trivial \}}\ \rangle \\
 & x_1 + \log_2 y_1 + x_2 + \log_2 y_2 \\
=&\langle\ cong_2\ (\lambda\ x\ y \rightarrow x + \log_2 y_1 + y + \log_2 y_2) \log_2 [ 2ˣ ]{\equiv}x\ \log_2 [ 2ˣ ]{\equiv}x\ \rangle \\
 &\log_2 2^{x_1} + \log_2 y_1 + \log_2 2^{x_2} + \log_2 y_2 \\
=&\ cong_2\ (\textunderscore{+}\textunderscore)\ (\log_2 [ a * b ]{\equiv}\log_2 a {+} \log_2 b\ \ 2^{x_1}\ y_1)\ (\log_2 [ a * b ]{\equiv}\log_2 a {+} \log_2 b\ \ 2^{x_2}\ y_2) \\
 & \log_2 (2^{x_1} * y_1) + \log_2 (2^{x_2} * y_2) \\
=&\langle\ \text{\{ apply \}} b^x * y = a\ \rangle\\
 & \log_2 a + \log_2 b \\
\end{align*}
$$

A particular thing to notice from the result of this proof is that
adding two $\log$ tuples together means that the integer components
need to be added and the remainder components need to be multiplied,
highlighting the deep relation this specification has with the
logarithmic properties.

## Formalization in Agda

First the required imports. Note that we are going to be using Agda's unnormalised rational number representation because they are easier to work with.

```agda
open import Data.Nat renaming (_/_ to _/ₙ_)
open import Data.Nat.Properties using (≤-trans ; m≤m+n)
open import Data.Integer.Base as ℤ using (ℤ ; +_)
open import Data.Integer.Properties as ℤ using ()
open import Data.Rational.Unnormalised renaming (_*_ to _*ℚᵘ_) using (ℚᵘ; _/_; truncate; _≃_; *≡*; ↧_; ↥_)
open import Data.Rational.Unnormalised.Properties as ℚᵘ using (↥[n/d]≡n; ↧[n/d]≡d)
open import Relation.Binary.PropositionalEquality
open import Data.Bool.Base
open import Data.Unit
open import Data.Nat.Logarithm
open import Function.Bijection
```

Then some auxiliary lemmas that will be useful mostly for providing non-zeroness proofs.

```agda
b^n>0 : ∀ (b n : ℕ) .⦃ _ : NonZero b ⦄ → b ^ n > 0
b^n>0 _ zero = s≤s z≤n
b^n>0 (suc b) (suc n) = ≤-trans (b^n>0 (suc b) n) (m≤m+n (suc b ^ n) _)

b^n-NZ : ∀ (b n : ℕ) .⦃ _ : NonZero b ⦄ → NonZero (b ^ n)
b^n-NZ b n = >-nonZero (b^n>0 b n)

*-NZ : ∀ a b .⦃ _ : NonZero a ⦄ .⦃ _ : NonZero b ⦄ → NonZero (a * b)
*-NZ (suc a) (suc b) = record { nonZero = tt }

↧[a*b]≡↧a*↧b : ∀ a b → ↧ (a *ℚᵘ b) ≡ ↧ a ℤ.* ↧ b
↧[a*b]≡↧a*↧b a@record{} b@record{} = refl

↥[a*b]≡↥a*↥b : ∀ a b → ↥ (a *ℚᵘ b) ≡ ↥ a ℤ.* ↥ b
↥[a*b]≡↥a*↥b a@record{} b@record{} = refl
```

Finally, here's the `LogMod` representation. Following the same idea as in the Agda standard-library for [`DivMod`](https://agda.github.io/agda-stdlib/Data.Nat.DivMod.html#18810), it has an integer field `w` (`w` for whole), a remainder field and a proof that `w` and `r` are related by the property found on section [Finding a way to recover the lost information](#finding-a-way-to-recover-the-lost-information).

```agda
record LogMod (base : ℕ) (a : ℕ) .⦃ _ : NonZero base ⦄ .⦃ _ : NonZero a ⦄ : Set where
  field
    w : ℕ
    r : ℚᵘ
    property : (+ a / 1) ≃ (+ (base ^ w) / 1) *ℚᵘ r
``` 

We are going to need an operation that is able to add two `LogMod`s together, as we seen previously the integer components are added and the remainder components are multiplied. Notice how a proof that adding the integer component and multiplying the remainder component is correct is also required.

```agda
_+ₗ_ : ∀ {a b c} .⦃ _ : NonZero a ⦄ .⦃ _ : NonZero b ⦄ .⦃ _ : NonZero c ⦄ .⦃ _ : NonZero (a * c) ⦄
      → LogMod b a → LogMod b c → LogMod b (a * c)
_+ₗ_ {a} {b} {c} record { w = w ; r = r ; property = p }
                record { w = w' ; r = r' ; property = p' } =
                record { w = w + w'
                       -- should be (r + r') but or I can't figure out how to write the property
                       -- proof with opaque variables. Instead, I write the inlined value
                       ; r = (+ (a * c) / (b ^ (w + w'))) ⦃ b^n-NZ b (w + w')⦄
                       ; property = *≡* (begin
                           + (a * c) ℤ.* (↧ (+ (b ^ (w + w')) / 1 *ℚᵘ (+ (a * c) / (b ^ (w + w'))) ⦃ b^n-NZ b (w + w') ⦄))
                             ≡⟨ cong (+ (a * c) ℤ.*_) (↧[a*b]≡↧a*↧b (+ (b ^ (w + w')) / 1) ((+ (a * c) / (b ^ (w + w'))) ⦃ b^n-NZ b (w + w') ⦄)) ⟩
                           + (a * c) ℤ.* (↧ (+ (b ^ (w + w')) / 1) ℤ.* (↧ (+ (a * c) / (b ^ (w + w'))) ⦃ b^n-NZ b (w + w') ⦄))
                             ≡⟨ cong₂ (λ x y → + (a * c) ℤ.* (x ℤ.* y)) (↧[n/d]≡d (+ (b ^ (w + w'))) 1) (↧[n/d]≡d (+ (a * c)) (b ^ (w + w')) ⦃ b^n-NZ b (w + w') ⦄) ⟩
                           + (a * c) ℤ.* (+ 1 ℤ.* + (b ^ (w + w')))
                             ≡⟨ cong (+ (a * c) ℤ.*_) (ℤ.*-identityˡ (+ b ^ (w + w'))) ⟩
                           + (a * c) ℤ.* + (b ^ (w + w'))
                             ≡⟨ ℤ.*-comm (+ (a * c)) (+ (b ^ (w + w'))) ⟩
                           + (b ^ (w + w')) ℤ.* + (a * c)
                             ≡˘⟨ cong₂ ℤ._*_ (↥[n/d]≡n (+ (b ^ (w + w'))) 1) (↥[n/d]≡n (+ (a * c)) (b ^ (w + w')) ⦃ b^n-NZ b (w + w') ⦄) ⟩
                           ↥ (+ (b ^ (w + w')) / 1) ℤ.* ↥ ((+ (a * c) / (b ^ (w + w'))) ⦃ b^n-NZ b (w + w') ⦄)
                             ≡˘⟨ ↥[a*b]≡↥a*↥b (+ (b ^ (w + w')) / 1) ((+ (a * c) / (b ^ (w + w'))) ⦃ b^n-NZ b (w + w') ⦄) ⟩
                           ↥ (+ (b ^ (w + w')) / 1 *ℚᵘ (+ (a * c) / (b ^ (w + w'))) ⦃ b^n-NZ b (w + w') ⦄)
                             ≡˘⟨ ℤ.*-identityʳ (↥ (+ (b ^ (w + w')) / 1 *ℚᵘ (+ (a * c) / (b ^ (w + w'))) ⦃ b^n-NZ b (w + w') ⦄)) ⟩
                           ↥ (+ (b ^ (w + w')) / 1 *ℚᵘ (+ (a * c) / (b ^ (w + w'))) ⦃ b^n-NZ b (w + w') ⦄) ℤ.* + 1
                             ≡⟨ cong (↥ (+ (b ^ (w + w')) / 1 *ℚᵘ (+ (a * c) / (b ^ (w + w'))) ⦃ b^n-NZ b (w + w') ⦄) ℤ.*_) (↧[n/d]≡d (+ (a * c)) 1) ⟩
                           ↥ (+ (b ^ (w + w')) / 1 *ℚᵘ (+ (a * c) / (b ^ (w + w'))) ⦃ b^n-NZ b (w + w') ⦄) ℤ.* ↧ (+ (a * c) / 1)
                             ∎)
                       }
     where
       open Data.Rational.Unnormalised.ℚᵘ
       open ≡-Reasoning
```

Equality relation for `LogMod` types.

```agda

infix 4 _≡ₗ_
data _≡ₗ_ {a b c} .⦃ _ : NonZero a ⦄ .⦃ _ : NonZero b ⦄ .⦃ _ : NonZero c ⦄ (x : LogMod b a) (y : LogMod b c) : Set where
  reflₗ : a ≡ c → x ≡ₗ y

```

Defining $\log_2$ function on natural numbers. This function does no lose information.

```agda
log₂ : ∀ a .⦃ _ : NonZero a ⦄ → LogMod 2 a
log₂ a = record
  { w = i
  ; r = ((+ a) / (2 ^ i)) ⦃ b^n-NZ 2 i ⦄
  ; property = *≡* (begin
      + a ℤ.* (↧ (+ (2 ^ i) / 1 *ℚᵘ (+ a / (2 ^ i)) ⦃ b^n-NZ 2 i ⦄))
        ≡⟨ cong (+ a ℤ.*_) (↧[a*b]≡↧a*↧b (+ (2 ^ i) / 1) ((+ a / (2 ^ i)) ⦃ b^n-NZ 2 i ⦄)) ⟩
      + a ℤ.* ((↧ (+ (2 ^ i) / 1)) ℤ.* ↧ ((+ a / (2 ^ i)) ⦃ b^n-NZ 2 i ⦄))
        ≡⟨ cong₂ (λ x y → + a ℤ.* (x ℤ.* y)) (↧[n/d]≡d (+ (2 ^ i)) 1) (↧[n/d]≡d (+ a) (2 ^ i) ⦃ b^n-NZ 2 i ⦄) ⟩
      + a ℤ.* (+ 1 ℤ.* + (2 ^ i))
        ≡⟨ cong (+ a ℤ.*_) (ℤ.*-identityˡ (+ (2 ^ i))) ⟩
      + a ℤ.* + (2 ^ i)
        ≡⟨ ℤ.*-comm (+ a) (+ (2 ^ i)) ⟩
      + (2 ^ i) ℤ.* + a
        ≡˘⟨ cong (+ (2 ^ i) ℤ.*_) (↥[n/d]≡n (+ a) (2 ^ i) ⦃ b^n-NZ 2 i ⦄) ⟩
      ↥ (+ (2 ^ i) / 1) ℤ.* ↥ ((+ a / (2 ^ i)) ⦃ b^n-NZ 2 i ⦄)
        ≡˘⟨ ↥[a*b]≡↥a*↥b (+ (2 ^ i) / 1) ((+ a / (2 ^ i)) ⦃ b^n-NZ 2 i ⦄) ⟩
      ↥ (+ (2 ^ i) / 1 *ℚᵘ (+ a / (2 ^ i)) ⦃ b^n-NZ 2 i ⦄)
        ≡˘⟨ ℤ.*-identityʳ (↥ (+ (2 ^ i) / 1 *ℚᵘ (+ a / (2 ^ i)) ⦃ b^n-NZ 2 i ⦄)) ⟩
      (↥ (+ (2 ^ i) / 1 *ℚᵘ (+ a / (2 ^ i)) ⦃ b^n-NZ 2 i ⦄)) ℤ.* + 1 ∎)
  }
  where
    i = ⌊log₂ a ⌋
    open ≡-Reasoning

_ : log₂ (20 * 20) ≡ₗ (log₂ 20 +ₗ log₂ 20)
_ = reflₗ refl
```

There's a small caveat with our `LogMod` representation, hence with our $\log_2$ function: it is not bijective. `LogMod` allows for more than one representation for the same arguments as mentioned in the comments on the next code snippet. For example, although both are semantically equal, the result of computing `LogMod 2 9` is different than calculating `LogMod 2 3 +ₗ LogMod 2 3`, because, in the latter, when the remainders are multiplied we get a value that is greater than the logarithm's base ($2$). This means that the remainder carries to much information and that this information should be carried over to the integer component of the `LogMod` type.

Equality for these terms holds due to the fact that their semantics is guaranteed by the `property` field. However this means that if we try to write the floored version of the logarithm function as the composition of two other functions we can not establish a one-to-one correspondance with the original function without any tricks.

```agda
-- This holds, however:
-- log₂ (3 * 3)    = (3, 9/8)
-- log₂ 3 +ₗ log₂ 3 = (2, 9/4)
_ : log₂ (3 * 3) ≡ₗ (log₂ 3 +ₗ log₂ 3)
_ = reflₗ refl

log₂[a*b]≡ₗlog₂a+ₗlog₂b : ∀ {a b} .⦃ _ : NonZero a ⦄ .⦃ _ : NonZero b ⦄ .⦃ _ : NonZero (a * b) ⦄
                      → log₂ (a * b) ≡ₗ log₂ a +ₗ log₂ b
log₂[a*b]≡ₗlog₂a+ₗlog₂b = reflₗ refl

⌊log₂′_⌋ : (n : ℕ) .⦃ _ : NonZero n ⦄ → ℕ
⌊log₂′ n ⌋ = LogMod.w (log₂ n)
-- ^ BUT: ⌊log₂′ n ⌋ ≢ ⌊log₂ n ⌋


⌊log₂′′_⌋ : (n : ℕ) .⦃ _ : NonZero n ⦄ → ℕ
⌊log₂′′ n ⌋ = LogMod.w (log₂ n) + ℤ.∣ truncate (LogMod.r (log₂ n)) ℤ./ (+ 2) ∣
--  ⌊log₂′′ n ⌋ ≡ ⌊log₂ n ⌋ very hard to prove

```

## Future Work

How well does this generalize to other types? What about generalizing the reasoning behind finding a suitable way of recovering the lost information of a computation on natural numbers for hyper-operations?
