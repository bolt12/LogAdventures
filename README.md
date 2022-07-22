# LogAdventures (**IN PROGRESS**)

I plan to write this as an Agda literate file, but I haven't been able to formalize it all in Agda yet. Because of this some of the equational reasoning style proofs are written in the way you would do it in Agda: using Agda's lemma names you might be familiar except when there's no suitable lemma yet or when the reasoning is rather trivial I just ommit the lemma at all.

## Context

This year I decided to start reading Chris Okasaki's book "Purely Functional data Structures" and try to solve all the exercises in Agda, going the extra mile and proving stuff about the data structures along the way. In Chapter 3, exercise 3.1. it asks us to prove that the right spine of a leftist heap of size `n` contains at most `logfloor2 (n + 1)` elements. All the solutions I looked at justified this argument via induction but in written form, not actually machine-checked proofs, so I thought this could be interesting to attempt in Agda. Turns out Agda didn't have any support for logarithms (base 2) at the time so I had to first tackle that issue (here: ...). I successfully got log working in Agda and successfully proved the exercise.

This is the context to how I started to explore this theme a little more. You see the thing I achieved was only so useful. Turns out the floored/ceiled version of log are much less expressive when having such an implementation over natural numbers. Properties such as `logfloor (a * b) = logfloor a + logfloor b` only hold up to `_<=_` for my implementation because it loses information in each recursive step, particularly, information about the remainder (fractional part of the result). Division on natural numbers is similar in this sense, but we can recover this information lost, i.e. make division bijective by computing its remainder (hence obtaining the famous `divMod` function) and relating it with its quotient result via the known `dividend = divisor * quotient + remainder`. Unfortunately information loss does interfere with well-behaved (useful & property-rich) compositionality. With this being said, is it there a feasable way of extending log and making it bijective in a way that flooring it would be just something of this form: `⌊_⌋ ∘ log b` ?

## Finding a way of making `log` bijective

I started by looking online and it might have been o my framing of the question or the search engine I was using, but I didn't really find anything particularly useful nor illuminating about this topic. After researching it myself, the main struggle I found is that the remainder of a log computation also behaves logarithmic-ally so I could not envision how an elegant specification for it can look... my attempts were in the form of `log b a = (x, r) => a = b ^ x + r and r = log b a - x = log b a`, so the integer part of the result is applied to the inverse function and an additive remainder, much like what happens in the `div` case. Addition (`b^x + r`) in the argument to `log b` might struck as fishy to some, I guess because no simple properties involve logs of sums. In contrast, there are useful properties for multiplying, dividing sums.

Much like division is the hard dual/inverse of multiplication, logarithm is the hard dual/inverse of exponentiation, i.e. it is much easier to multiply/exponentiate than it is to divide/log. Having said this, since exponentiation is dual to logarithm then surely the specification that relates the computation's remainder and result will be also related via exponentiation! Maybe we will have a better chance gaining insights into logarithms by studying their simpler dual.

I started by trying to figure out how to compute `log₂ 20` by hand, which is around `4.31` so `4` integer part and `0.321` fractional part. I am looking for a way to relate the fractional part with the integer part, but before that I need to start by figuring out how I can obtain it. I tinkered a bit with what could be a possible algorithm  and reached the following: `x = log₂ 20 ⇔ 2ˣ = 20`, leveraging the inverse relationship (I tried working on the easy, dual, exponential end), so in order to write `20` as a power of two, I decompose `20` into the closest power of `2` (which is `2⁴`) times some remainder (or plus some remainder since we are in an exponent position). So something of this form  `2⁴ × 2ʸ ≡ 2⁴⁺ʸ and 2⁴⁺ʸ ≡ 20` needs to be true. Notice how `x` is now of the form `x = (i + r)` (`i`integer + `r`emainder) just like we are aiming for; and how the inverse reasoning could be done but with logarithms instead of exponentiation, but this way around would arguably be harder.

Solving the last equation for `y` gives us `2ʸ ≡ 20 / 2⁴ ≡ 20 / 16 ≡ 5 / 4`, so applying the inverse relation again `y ≡ log₂ (5 / 4)`, the remainder is found! And indeed `log₂ (5 / 4)` is around `0.321` (i.e. the fractional part of `log₂ 20`). But this is in `log` form you say, I can not compute that! Fair point but notice the `y` is actually supposed to be in an exponent position and we know that `x ≡ 2ˡᵒᵍˣ` (`log₂ x` as the super script) holds ! So we actually get:

```agda
2⁴⁺ˡᵒᵍ⁵⁄⁴    ≡⟨ ^-distribˡ-+-* 2 4 (5 / 4) ⟩
2⁴ * 2ˡᵒᵍ⁵⁄⁴ ≡⟨ cong (2⁴ *_) 2ˡᵒᵍˣ≡x ⟩
2⁴ × (5/4)   ≡⟨⟩
16 * (5/4)   ≡⟨⟩
20           ∎
```

So if we have something like `divMod` but for `log` where `log b a = (x , y)`, where `x` is the integer part and `y` is the remainder as explained above, then this is the specification that tights everything together: `bˣ * y ≡ a`. A multiplicative rather than additive remainder relating to an additive remainder in the exponent. And substituting `a` with the left hand part we get:

```agda
log₂ (2ˣ * y)    ≡⟨ log₂[a*b]≡log₂a+log₂b 2ˣ y ⟩
log₂ 2ˣ + log₂ y ≡⟨⟩
x + log₂ y       ∎
```

And this form is the final destination of this journey if one would go via log instead. My first hunch was that the remainder behaved logarithimic-ally and indeed I have seem to prove myself right, and some reader might be able to reach this final form immedeatly, but I'd argue this way wouldn't be as insightful.

There are a couple of things I still have to think better through:

1. Remainder will not be an integer/natural.
2. Does this formulation allow me to get the `log₂ (a*b)≡log₂ a + log₂ b`, et al? How ?
3. How well does this generalize to other types?
4. ?

### 1.

Regarding the first point, I received the following comment:

> If we let `(x,y)  = (a div b, a mod b)` then we have `x * b + y = a`. If we let `(x, y) = (log_b a, logmod_b a)` then we have `bˣ * y  = a`.  The structure seems similar. The only weird thing is that `y` has to be rational, not natural.

Yes, the structure is very similar. And I hope to be hinting at some way of generalizing this reasoning for other operations! For the integer/result part, one applies the inverse function (`_*_` for `div` and `_^_` for `log`), for the fractional/remainder part, the remainder is added in the `divMod` case, but multiplied in the `log` case. The trick is to see that in the `log` case you are actually adding the remainder too but in an exponential position and that translates to multiplication!

This comment also pointed to the fact that the remainder is not natural, which kind of lead me to think it might be a flaw on my conclusions. Further investigation got me closer to a clearer relation between the the two specifications:

Division is the inverse of multiplication via `a / b ≡ x ⇔ x * b ≡ a`. If I make `x` be the sum of an integer part (`x`) with a fractional part (`y`) `x + y` then, substituting `x` one gets 

```agda
(x + y) * b ≡ a    ≡⟨ *-distribʳ-+ b x y ⟩
 x * b + y * b = a ∎
```

This is very close to the `divMod` property for natural numbers, the insight comes by the fact (coincidence?) That `y * b` is always an integer. So for natural number division the formula can be simplified to `x * b + y` but if we wanted a rational number as our remainder we'd have to use `x * b + y * b`. Proof that y * b is always integer: 

Given that `a * x + b * y ≡ a ⇔ b * y ≡ a - a * x` and since `a` and `a * x` are integers, and integers are closed under subtraction, `y * b` is an integer.

I like to think this more a coincidence than a fact because, at least in my case, I only have heard about the `divMod` property where the remainder is an integer/natural and would take this for granted. Taking this for granted actually steered me in the wrong direction in the beginning because I was trying very hard to also have an additive integer remainder without first stopping to think about why. I hope this also intrigues whoever is reading this.

### 2.

Regarding the second point:

Gave this a go and if we take one particular example `log₂ (20 * 20) ≡ log₂ 20 + log₂ 20`:

```agda
log₂ (20 * 20)        ≡⟨ log₂[a*b]≡log₂a+log₂b _ _ ⟩
log₂ 20 + log₂ 20     ≡⟨⟩
(4 , 5/4) + (4 , 5/4) ≡⟨ here I had to use the calculator and some trial and error
                         to figure out what a suitable definition for _+_ could be
                       ⟩
(4 + 4 , 5/4 * 5/4)   ≡⟨⟩
(8, 25/16)
```

I reached a sound definition of addition on log, but to double check, let's apply these arguments to the `bˣ * y  ≡ a` property, where `b ≡ 2`, `x ≡ 8` and `y ≡ 25/16`: `2⁸ * 25/16 ≡ 20 * 20`. Hurray!

Now, how to derive this from the generic formula?

```agda
-- assume log₂ a ≡ (x₁ , y₁) and log₂ b ≡ (x₂ , y₂)
log₂ (a * b) ≡ log₂ a + log₂ b                 ≡⟨ apply bˣ * y  ≡ a⟩
log₂ ((2^x₁ * y₁) * (2^x₂ * y₂))               ≡⟨ note that y ≡ 2 ^ log₂ y ⟩
log₂ ((2^(x₁ + log₂ y₁)) * (2^(x₂ + log₂ y₂))) ≡˘⟨ cong log₂ (^-distribˡ-+-* 2 (x₁ + log₂ y₁) (x₂ + log₂ y₂) ⟩
log₂ ((2^(x₁ + log₂ y₁ + x₂ + log₂ y₂)))       ≡⟨ log₂[2ˣ] ≡ x ⟩
(x₁ + log₂ y₁ + x₂ + log₂ y₂)                  ≡⟨⟩
(x₁ + x₂ + log₂ y₁ + log₂ y₂)                  ≡˘⟨ cong (λ x → x₁ + x₂ + x) (log₂[a*b]≡log₂a+log₂b y₁ y₂) ⟩
(x₁ + x₂ + log₂ (y₁ * y₂))
```

This reasoning clearly explains why we need to multiply the remainders and add the results.
 
Does this addition operator on a tuple remind you of any particular useful algebraic structure? One where the 1st component is added and the second multiplied? I am looking for insights!

### 3.

Regarding the third point I still do not have any particular comments, I hope that once I am able to fully formalize this in Agda I can then maybe start thinking about it more deeply.

## Conclusions

So far I am very happy with the way everything is unfolding, I think I am onto something but only time will tell. As I said in the beginning I haven't found anything remotely similar to what I just described online, not even about the coincidental fact that division on natural numbers can have a natural remainder. If you by any chance are familiar with something point it my way!

I hope I am able to formalize all this in Agda and see what kind of insights I fall into. Currently I am still thinking what's the best approach to encode this in Agda, I will probably keep it simple and deal only with base `2` logs and still have to decide if I want to work with integers or rationals as the domain. Tips and suggestions are appreciated!
