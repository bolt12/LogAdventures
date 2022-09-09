# LogAdventures (**IN PROGRESS**)

I plan to write this as an Agda literate file, but I haven't been able to formalize it all in Agda yet. In the meantime I'll use Github's LateX support and write my equational reasoning proofs in somewhat the way you would do it in Agda (using Agda's lemma names you might be familiar except when there's no suitable lemma yet or when the reasoning is rather trivial I just omit the lemma at all).

## Context

This year I decided to start reading Chris Okasaki's book "Purely Functional data Structures" and try to solve all the exercises in Agda, going the extra mile and proving stuff about the data structures along the way. In Chapter 3, exercise 3.1. it asks us to prove that the right spine of a leftist heap of size $n$ contains at most $\lfloor \log_2 (n + 1) \rfloor$ elements. All the solutions I looked at justified this argument via induction but in written form, not actually machine-checked proofs, so I thought this could be interesting to attempt in Agda. Turns out Agda didn't have any support for logarithms (base 2) at the time so I had to first tackle that issue (see [here](https://github.com/agda/agda-stdlib/pull/1782)). I successfully got truncated log working in Agda and successfully proved the exercise.

This is the context to how I started to explore this theme a little more. You see the truncated log is only so useful and doesn't get some very useful proofs. The floored/ceiled version of $\log$ is much less expressive and properties such as $\lfloor \log_2 (a * b)\rfloor = \lfloor \log_2 a\rfloor + \lfloor \log_2 b\rfloor$ only hold up to $\textunderscore \leq \textunderscore$ for my implementation because it loses information in each recursive step, particularly, information about the fractional part of the result. Division on natural numbers is similar in this sense, but we can recover lost information, i.e. make division bijective by computing its remainder (hence obtaining the famous `divMod` function) and relating it with its quotient result via the known $dividend = divisor * quotient + remainder$ property. Unfortunately, information loss does interfere with well-behaved (useful & property-rich) compositionality. With this being said, is it there a feasible way of extending $\log$ and making it bijective in a way that flooring it would be just something of this form: $\lfloor \textunderscore \rfloor \circ \log b$ ?

## Finding a way of making $\log_2$ bijective

I started by looking online and it might have been the way I framed the question or the search engine I was using, but I didn't really find anything particularly useful nor illuminating about this topic. After researching it myself, the main obstacle I found was that the remainder (I'll refer to the fractional part of the $log_2$ result as 'remainder') of a $\log_2$ computation also behaves logarithmic-ally so I could not envision how an elegant specification for it can look... my attempts started in the form of $\log_b a = (x, r) \implies a = b^x + r$, so the integer part of the result is applied to the inverse function and an additive remainder, much like what happens in the division case. Addition ( $b^x + r$ ) in the argument to $\log_b$ might seem a little fishy to some, I guess this uneasy feeling is due to the fact that there are no known simple properties which involve $\log$ of sums. In contrast, there are useful properties for multiplying, dividing sums!

Much like division is the hard dual/inverse of multiplication, logarithm is the hard dual/inverse of exponentiation, i.e. it is much easier to multiply/exponentiate than it is to divide/log. Having said this, since exponentiation is dual to the logarithm then surely the specification that relates the computation's remainder and integer part will be also related via exponentiation! Maybe we will have a better chance obtaining insights by studying logarithm's simpler dual.

I started by trying to figure out how to compute $\log_2 20$ by hand, which is around $4.321$ so $4$ integer part and $0.321$ fractional part. I am looking for a way to relate the fractional part with the integer part, but before that I need to start by figuring out how I can obtain it. I tinkered a bit with what could be a possible algorithm and reached the following: $x = \log_2 20 \iff 2^x = 20$, leveraging the inverse relationship (I preferred working on the easy, dual, exponential end), so in order to write $20$ as a power of two, I decomposed $20$ into the closest power of $2$ (which is $2^4$) multiplied by some remainder (I should say plus some remainder since we are in an exponent position). So something of this form  $2^4 * 2^y = 2^{4 + y} = 20$ needs to be true. Notice how $x$ from above is now composed of two parts $x = (i + r)$ ($integer + remainder$). Notice as well how the inverse reasoning could be done with logarithms instead of exponentiation, but this way around would be arguably harder.

Solving this last equation for $y$ gives us $2^y = 20 / 2^4 = 20 / 16 ≡ 5 / 4$, so applying the inverse relation again $y = \log_2 (5 / 4)$, the remainder is found! And indeed $\log_2 (5 / 4)$ is around $0.321$ (i.e. the fractional part of $\log_2 20$). But this is in $\log$ form you say, I can not compute that! Fair point but notice the $y$ is actually supposed to be in an exponent position and we know that $x = 2^{\log_2 x}$ holds! So we actually get:

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

So if we have something like `divMod` but for $\log$ where $\log\ b\ a = (x , y)$, where $x$ is the integer part and $y$ is the remainder as explained above, then this is the specification that tights everything together:

$$
b^x * y = a
$$

A multiplicative rather than additive remainder in the logarithmic realm, relating to an additive remainder in the exponent realm. Substituting $a$ with the left hand part we get:

$$
\begin{align*}
 & \log_2 (2^x * y) \\
=&\langle\ \log_2 [ a * b ]{\equiv}\log_2 a {+} \log_2 b\ \ 2^x\ \ y\ \rangle \\
 & \log_2\ 2^x + \log_2 y \\
=&\langle\ \text{\{ trivial \}}\ \rangle\\
 & x + \log_2 y \\
\end{align*}
$$

And this form is the last stop on this journey. As I said in the beginning, the remainder behaves logarithimic-ally and indeed this is higlighted in our reasoning. Some reader might have been able to reach this conclusions quicker, but I'd argue that without actually following the proofs it wouldn't be as insightful.

There are a couple of things I still have to think better through:

1. Remainder will not be an integer/natural, is it irrational?
2. Does this discoveries allow me to derive a correct algortithm for computing a bijective \log function that where $\log_2 (a * b) = \log_2 a + \log_2 b$, et al, hold? How ?
3. How well does this generalize to other types?
4. ?

### 1.

Regarding the first point, I received the following comment:

> If we let `(x,y)  = (a div b, a mod b)` then we have `x * b + y = a`. If we let `(x, y) = (log_b a, logmod_b a)` then we have `bˣ * y  = a`.  The structure seems similar. The only weird thing is that `y` has to be rational, not natural.

Yes, the structure is very similar. And I hope to be hinting at some way of generalizing this reasoning for other operations! For the integer/result part, one applies the inverse function (`_*_` for `div` and `_^_` for `log`), for the fractional/remainder part the remainder is added in the `divMod` case, but multiplied in the `log` case. The trick is to see that in the `log` case you are actually adding the remainder too but in an exponential position and that translates to multiplication!

This comment also pointed to the fact that the remainder is not natural, which kind of lead me to think it might be a flaw on my conclusions. Further investigation got me closer to a clearer relation between the two specifications:

Division is the inverse of multiplication via $a / b = x \iff x * b = a$. If I make $x$ be the sum of an integer part ( $i$ ) with a fractional part ( $r$ ) $i + r$ then, substituting $x$ one gets

$$
\begin{align*}
 & (i + r) * b = a \\
=&\langle\ \ast\text{\{ - \}}{distrib^r}\text{\{ -+ \}}\ b\ x\ y\ \rangle\\
 & i * b + r * b = a \\
\end{align*}
$$

This is very close to the `divMod` property for natural numbers, the insight comes by the fact (coincidence?) That $r * b$ is always an integer. So for natural number division the formula can be simplified to $i * b + r$ but if we wanted a rational number as our remainder we'd have to use $i * b + r * b$. Proof that $r * b$ is always integer:

Given that $a * i + b * r = a \iff b * r = a - a * r$ and since $a$ and $a * i$ are integers, and integers are closed under subtraction, $r * b$ is an integer.

I like to think this more a coincidence than a fact because, at least in my case, I only have heard about the `divMod` property where the remainder is an integer/natural and would take this for granted. Taking this for granted actually steered me in the wrong direction in the beginning because I was trying very hard to also have an additive integer remainder without first stopping to think about why. I hope this also intrigues whoever is reading this.

### 2.

Regarding the second point:

Gave this a go and if we take one particular example $\log_2 (20 * 20) = \log_2 20 + \log_2 20$:

$$
\begin{align*}
 & \log_2 (20 * 20) \\
=&\langle\ \log_2 [ a * b ]{\equiv}\log_2 a {+} \log_2 b\ \textunderscore\ \textunderscore\ \rangle\\
 & \log_2 20 + \log_2 20 \\
=&\langle\ \text{\{ trivial \}}\ \rangle \\
 & (4 , 5 / 4) + (4 , 5 / 4) \\
=&\langle\ \text{\{ here I had to use the calculator and some trial and error \}} \\
 &\ \ \text{\{ to figure out what a suitable definition for _+_ could be \}}\ \rangle \\
 & (4 + 4 , 5/4 * 5/4) \\
=&\langle\ \text{\{ trivial \}}\ \rangle \\
 & (8 , 25 / 16) \\
\end{align*}
$$

I reached a sound definition of addition on log, but to double check, let's apply these arguments to the $b^x * y = a$ property (where $b = 2$, $x = 8$ and $y = 25 / 16$): $2^8 * 25 / 16 = 20 * 20$. Hurray!

Now, how to derive this from the generic formula?

$$
\text{\{ Assume \} \log_2 a = (x_1 , y_1) \text{\{ and \} \log_2 b = (x_2 , y_2)
\begin{align*}
 & \log_2 (a * b) = \log_2 a + \log_2 b \\
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
=&\langle\ cong\ (\lambda x \rightarrow x_1 + x_2 + x) (\log_2 [ a * b ]{\equiv}\log_2 a {+} \log_2 b\ \ y₁\ y₂)\ \rangle \\
 & x_1 + x_2 + \log_2 (y_1 * y_2) \\
\end{align*}
$$

This reasoning clearly explains why we need to multiply the remainders and add the results.

Does this addition operator on a tuple remind you of any particular useful algebraic structure? One where the 1st component is added and the second multiplied? I am looking for insights!

### 3.

Regarding the third point I still do not have any particular comments, I hope that once I am able to fully formalize this in Agda I can then maybe start thinking about it more deeply.

## Conclusions

So far I am very happy with the way everything is unfolding, I think I am onto something but only time will tell. As I said in the beginning I haven't found anything remotely similar to what I just described online, not even about the coincidental fact that division on natural numbers can have a natural remainder. If you by any chance are familiar with something point it my way!

I hope I am able to formalize all this in Agda and see what kind of insights I fall into. Currently I am still thinking what's the best approach to encode this in Agda, I will probably keep it simple and deal only with base $2$ logarithms and still have to decide if I want to work with integers or rationals as the domain. Tips and suggestions are appreciated!
