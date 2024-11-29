java c
1 Sequent calculus Your task is to implement thesequent calculus   in   Haskell.    In the mandatory part   of the   project,   you   will   omit   implication   →   and   bi-implication   $   and   construct   proofs   as   explained   on   pages   126–127   of the   textbook   using   the   rules   given   there:
In   the   optional   part,   you   will   add   rules   for   →   and   $.
Recall   that   proofs   start   with   a   sequent   and   are   constructed   by   applying   rules,   working   upwards,   until you   reach simple premises involving   only“bare”predicates,   not   containing   any   connectives.   The   proof shows that the   sequent you   started   with   follows   from   those   premises.    If the   proof ends   in   the   empty   set   of simple   premises,   you   have   shown that   the   sequent you   started   with   is universally valid.
Here’s   an   example   of a   sequent   calculus   proof,   which   proves   that   F   ((¬p _ q) Λ ¬p) _p   is   universally   valid:

Here’s   another   example,   which   proves   that   F   ¬   ((¬a _ b) Λ   (¬c _ b)) _ (¬a _ c)   follows   from   a, b   F   c:
The   number   of   times   that   a   premise   appears   is   immaterial,   because   we’re   interested   in   the   set    of   premises   from   which   the   conclusion   holds.      In   this   proof,   the   premise   a, b   F   c   happens   to   appear   twice.There’s   often   more   than   one   proof   starting   from   a   given   sequent,   but   all   end   with   the   same   set   of   premises.    Because   each   rule   of   the   sequent   calculus   eliminates   one   connective   from   an   antecedent   or   a   succedent,   proofs   always   terminate.
2 Implementing sequent calculus in Haskell 
To   implement   the   sequent   calculus   in   Haskell,   you   will   start   with   an   algebraic   datatype   similar   to   the   one   in   FP   Tutorial   6   that   deﬁnes   propositions   with   variable   names   of type   String:
type Name   =   String
data Prop   = Var   Name
|   Not   Prop
|   Prop   :   || :   Prop
|   Prop   ::   Prop
|   Prop   :->:   Prop
|   Prop   :<->:   Prop
The   last   two   cases   will   be   required   only   for   the   optional   part   but   they   are   included   from   the   start   to   allow   the   optional   part   to   be   coded   as   a   simple   extension   of the   mandatory   part.
Sequents   are   deﬁned   as   follows:
data   Sequent   =   [Prop]   :   |=:   [Prop]
infix   0   :   |   =:
We use unordered lists of propositions, possibly with   repetitions,   to   represent   the   sets   of antecedents   and   succedents   of sequents.You   are   provided   with   a   ﬁle   Sequent   .hs   containing   the   above   type   deﬁnitions   together   with   code   for   declaring   Prop and      Sequent as   instances   of   Show and    (for   purposes   of   QuickCheck   test      case   generation) of Arbitrary.   If you want to use   QuickCheck to test   your   code   (strongly   recommended!   always   test   your   code!)    then   you   will   need   to   comment   out   the   following   two   lines   for   generating   test   cases   that   include   →   and 艹 until   you   get   to   the   optional   part:
,   liftM2   (:->:) p2 p2
,   liftM2   (:<->:) p2 p2
Don’t   make   any   other   changes   to   Sequent   .hs.
Also   provided   is   a   skeleton   ﬁle   called   Project   .hs   which   imports   Sequent.   Your job   is   to   deﬁne   the   function
prove   :: Sequent   ->   [Sequent]in   Project   .hs   which,   when   applied   to   a   sequent,   produces   the   list   of   simple   sequents   from   which   that   sequent   follows   according   to   a   sequent   calculus   proof.    You   need   not   produce   the   proof   itself,   just   the   list   of premises.
For   the   ﬁrst   example   above,   it   should   produce
> p   =   Var   "p"
>   q   =   Var   "q"
> prove   ([]   :   |   =:   [((Not p   :   || :   q)   ::   Not   p)   :   || :   p])
[]
For   the   second   example,   one   correct   result   would   be
>   a   =   Var   "a"
> b   =   Var   "b"
>   c   =   Var   "c"
> prove   ([]   :   |   =:   [(Not   ((Not   a   :   || : b)   ::   (Not   c   :   || : b)))   :   || :   (Not   a   :   || :   c)])
[[a,b]   :   |=:   [c]]
Because   of our   use   of unordered   lists   to   represent   sets,   another   correct   result   would   be
> prove   ([]   :   |   =:   [(Not   ((Not   a   :   || : b)   ::   (Not   c   :   || : b)))   :   || :   (Not   a   :   || :   c)]) 
[[a,b]   :   |   =:   [c,c],[b,a,b]   :   |=:   [c]]
and   there   are   many   others. 
3 How to proceed 
How   you   proceed   is   up   to   you.      That’s   why   this   is   a   project   and   not   a   tutorial   exercise.
One   way   to   go   is   to   start   by   deﬁning   the   rules   of   sequent   calculus   as   Haskell   functions,   with   for   instance
orL   :: Sequent   -> Maybe   [Sequent]
Note that the result type   is Maybe   [Sequent].    We use    [Sequent]   rather   than   Sequent   because   the   _L rule   has   more   than   one   premise.   And   we   use   Maybe   [Sequent]   rather   than    [Sequent]   because   _L isn’t   applicable   to   all   sequents,   only   ones   having   an   antecedent   with   _ as   its   main   connective.         For   the   _R rule,   you   could   deﬁne   a   function
orR   :: Sequent   -> Maybe   Sequent
since   it   can   produce   at   most   one   premise,   but   it’s   probably   better   to   use   the   same   type   for   all   rules   for   the   sake   of the   next   step:
orR   :: Sequent   -> Maybe   [Sequent]
You   might   even   want   to   deﬁne   a   type   for   rules:
type Rule =   Sequent   -> Maybe   [Sequent]
orL,   orR   :: RuleHint: The    main   work   in    applying      a   rule   to      a   sequent   involves   ﬁnding      appropriate   items   in   the   antecedent   list   and/or   the   succedent   list   and   replacing   them   with   new   items.   You   might   ﬁnd   useful   functions   for   doing   this   in   Data.List.Now you   can use the   deﬁnitions of the   rules   to   search   for   a   proof.    Given   a   sequent, prove   tries   rules   until   one   applies   (that   is,   it   produces   Just seqs      instead   of   Nothing).    Then   do   that   to   each   of   the   sequents   in   seqs   .    Keep   going   until   none   of the   rules   applies.    The   result   is   a   list   of   simple   sequents   from   which   the   original   sequent   follows.
The   deﬁnition   of prove   will   probably   rely   on   helper   functions   that   try   individual   rules   and/or   lists   of rules.    How   you   do   this   is   up   to   you.
4          Optional Material: Adding implication and bi-implication Following   the   Common   Marking   Scheme,   a   student   with   good   mastery   of   the   material   is   expected   to   get   3/4   points.    This   section   is   for   demonstrating   exceptional   mastery   of   the   material.   It   is   optional   and   worth   1/4   points.
The   deﬁnitions of the types Prop   and   Sequent   already   allow for   them   to   contain   implication   →   and   bi-implication   艹.
Here   are   the   sequent   calculus   rules   for   these   connectives   from   page   222   of the   textbook:

Here   is   a   proof   that   a   →   b   F   ¬b   →   ¬a   is   universally   val代 写Sequent calculusMatlab
代做程序编程语言id,   using   these   rules   and   the   ones   given   earlier:

For   the   optional   part,   extend   your   function
prove   :: Sequent   ->   [Sequent]to dosequent calculus proofs of sequents involving propositions that may contain   implication   and/or   bi-implication.   Applying prove   to asequent that doesn’t contain implication orbi-implication should   produce the same result as before.    If you do the optional part, you don’t   have to   submit two   versions   of prove;   the   extended   version,   that   works   for   implications   and   bi-implications   as   well   as   the   other   connectives,   will   suﬃce.
For   the   example   above,   it   should   produce
>   a   =   Var   "a"
> b   =   Var   "b"
> prove   (a   :->: b   :   |=:   Not   b   :->:   Not   a)
[]If you   use   QuickCheck   for testing your   code,   remember to   restore   the   two   lines   of the   declaration   in   Sequent   .hs   that   Prop   is   an   instance   of Arbitrary   so   that   it   will   also   generate   test   cases   including   :->:   and      :<->:.
6 Marking 
The   programming   project   will   be   marked   by   your   tutor,   and   is   worth   20%   of the   mark   for   Inf1A.         Your   mark   on   the   scale   0–4   will   be   based   mainly   on   the   following   tests.    (Your   tutor   will   also   check   your   code   to   make   sure,   among   other   things,   that   it   is   not   written   to   pass   only    these   tests.)    The   tests   have   been   set   up   in   the   automarker.      They   will   be   run   every   time   you   submit   Project   .hs,   and   you   will   be   able   to   check   the   results.    You   can   submit    as   often   as   you   like,   but   only   the   last   submission   before   the   deadline   will   be   taken   into   account   in   the   marking.The   sequents   in the tests below   have been   typeset   to   make   them   a   little   easier   to   read,   but   of course   the   actual   tests   use   Haskell   syntax.   Because   of our   use   of unordered   lists   to   represent   tests,   lists   of   assumptions   that   are   equivalent   to   those   shown   as   results   are   also   correct.
To   get   1   point,   it’s   enough   that   any   one   of   the   following   one-step   proofs   is   correct.      Non-working   code   that   shows   some   sensible   work   may   also   be   awarded   1   point.
> prove   (   F   a   _ b         )         --   _R
[    F   a, b      ]
> prove   (   a _ b   F         )         --   _L
[   a   F         ,   b   F         ]
> prove   (   F   a   Λ b      )          --   ΛR
[   F   a       ,   F   b      ]
> prove   (   a Λ b   F         )          --   ΛL
[   a,   b   F         ]
> prove   (   F   ¬a      )               --   ¬R
[   a   F         ]
> prove   (   ¬a   F         )               --   ¬L
[    F   a      ]
> prove   (   a,b   F   b,c      )      --   I
[   ]
To   get   2   points,   the   following   proof,   which   uses   only   the   non-branching   rules,   must   also   be   correct.
> prove   (   F   (¬   (e Λ (f Λ ¬¬c))) _   (¬a _ c)         )   [   ]
To   get   3   points,   most   or   all   of the   following   proofs   must   also   be   correct.
> prove   (   F   ((¬a _ b) Λ ¬a) _   a         )   [   ]
> prove   (   F ¬   ((¬a _ b) Λ (¬c _ b)) _ ¬a _ c         )   [   a,   b   F   c      ]
> prove   ( ¬c _ (f _ b), (a _ d) Λ (b _ b) F   ¬   (d _ b),   ¬c _ (f   Λ e), (f   Λ b) _ (c Λ e),   ¬   (a _ c),   ¬e Λ (c _ e),   e          )   [   ]
> prove   ( (b _ f) _ (d _ c),   ¬   (d _ a),   ¬   (d Λ f),   ¬   (a Λ f), (a _ e) Λ (b _ c),   c   F            )
[ b,c,   e   F   a,d       , b,c,   e   F   a,d,f       , b,c,e,   f   F   a,d       , c,   e   F   a,d       , c,   e   F   a,d,f       , c,e,   f   F   a,   d      ]
> prove   ( b,(d _ b) _ ¬c,   ¬   (d Λ f) F   (b _ d) Λ (c Λ e), (a _ c) _ ¬f,   ¬   (f Λ f), (e Λ d) Λ (a _ d),c, (b Λ b) Λ (e _ b)       )   [   ]
> prove   ( (f _ a) Λ ¬f,(a _ a) Λ (c _ b),   ¬a _ ¬c,   ¬d _ (a _ d)
F   (f Λ d) _ (d _ d), (c _ e)   _ (d _   e), (b   _   a)   Λ (f _ e)       )
[   a,   b   F   c,d,e,   f      ]
> prove   ( (a _ b) _ ¬d,(e _ b) Λ ¬f   F   a, (f Λ f) _ (f Λ f),   ¬f Λ (e _ c), (f Λ b) Λ (e _ a)       )   [ b   F   a,e,c,f      ,   b   F   a,c,d,e,   f    ]
> prove   ( (a _ f) _ (c _ d), (b Λ f) _ (f _ a), (f _ f) Λ ¬f,   ¬a _ (c _ e) F ¬e Λ ¬c, (b Λ c) _ ¬a,   ¬   (e _ d)       )   [   ]
> prove   (   F   (d _ b) _ (e Λ a),   ¬f Λ (d   Λ b), (c Λ b) Λ ¬e, (c _ c) _ (d _ d),
¬e Λ (a Λ e), (a _ e) _ (c _ d), (d _ d) Λ ¬e, (c Λ d) Λ   ¬a, ¬   (e _ c)       )   [   ]
To   get   4   points,   most   or   all   of the   following   proofs   involving   implication   and/or   bi-implication   must   also   be   correct.
> prove   (   a   →   b   F   ¬b   →   ¬a          )   [   ]
> prove   (   (c _ d) →   (d Λ f), (a 艹 a) 艹   (b   _ a)   F   (c 艹 b)   艹   (b   →   a),   ¬   (b   _ d),   ¬   (b   Λ d), (d   艹   f)   →   (c _ e)          ) [   b,a,f,d   F   c,   e    ]
> prove   ( ¬   (f 艹 f),   ¬f   艹   (d 艹   e), (d   →   f)   艹   (a _ b)   F   (d Λ c) →   (c   艹   d),   ¬   (c   艹   e)         ) [   ]
> prove   (   (e →   b) →   (a →   f), (b _ a) _ ¬f,(d 艹 b) 艹   (f   Λ e)   F   (d 艹 d) _   (e   艹   c),   ¬   (d   →   f)         )   [   ]
> prove   (   (f _ b) Λ (b →   d), (e _ d) _ ¬e, (f   →   e) →   ¬f,(e _ d) Λ (d 艹 c),   ¬   (c 艹 b),   ¬f   Λ   (a   Λ a),
(f 艹 c) →   (c _ f) F   (e Λ f) _ (f Λ a),   ¬f Λ ¬d,(f _ c) 艹 (f 艹 b)       )   [   ]
> prove   (   (e Λ f) 艹   (a Λ e), (b _ d) Λ (f 艹 c),   ¬   (d 艹 f), (d Λ e) _ (c →   f), (e 艹 f)   艹   (b _ d) F   (e _ d) Λ ¬e          )   [   f,e,a,b,   c   F   d      ]The   challenge   part   isn’t   worth   any   points,   but   the   following   tests   are   included   in   the   automarker.   Correct for these means getting the same assumptions with a proof that is no   longer than   the   number   of rules   shown,   which   is   achieved   by   the   sample   solution.
> proveCount   ( (a _ f) _ (c _ d), (b Λ f) _ (f _ a), (f _ f) Λ ¬f,   ¬a _ (c _ e) F ¬e Λ ¬c, (b Λ c) _ ¬a,   ¬   (e _ d)       )   ([   ],   168)
> proveCount   ( ¬c _ (f _ b), (a _ d) Λ (b _ b) F   ¬   (d _ b),   ¬c _ (f   Λ e), (f Λ b) _ (c   Λ e),   ¬   (a _ c),   ¬e Λ (c _ e),   e          )   ([   ],   39)
> proveCount   ( b,(d _ b) _ ¬c,   ¬   (d Λ f) F   (b _ d) Λ (c Λ e), (a _ c) _ ¬f,   ¬   (f Λ f), (e Λ d) Λ (a _ d),c, (b Λ b) Λ (e _ b)   ([   ],   58)
> proveCount   (   (c _ d) →   (d Λ f), (a 艹 a) 艹   (b _ a) F   (c   艹   b)   艹   (b   →   a),   ¬   (b _ d),   ¬   (b Λ d), (d 艹 f)   →   (c   _ e)         )   ([ a,b,f,d   F   c,   e    ],   144)
> proveCount   ( ¬   (f 艹 f),   ¬f   艹   (d 艹 e), (d   →   f)   艹   (a   _ b)   F   (d Λ c) →   (c   艹   d),   ¬   (c   艹   e)         )   ([   ],   105)
> proveCount   (   (e →   b) →   (a →   f), (b _ a) _ ¬f,(d 艹 b) 艹   (f   Λ e) F   (d   艹   d) _   (e   艹   c),   ¬   (d   →   f)         )   ([   ],   306)
> proveCount   (   (f _ b) Λ (b →   d), (e _ d) _ ¬e, (f   →   e) →   ¬f,(e _ d) Λ (d 艹 c),   ¬   (c 艹   b),   ¬f   Λ   (a Λ a),
(f 艹 c) →   (c _ f) F   (e Λ f) _ (f Λ a),   ¬f Λ ¬d,(f _ c) 艹 (f 艹 b)       )
([   ],   229)
> proveCount   (   (e Λ f) 艹   (a Λ e), (b _ d) Λ (f 艹 c),   ¬   (d 艹 f), (d Λ e) _ (c →   f), (e 艹 f)   艹   (b   _ d)   F   (e _ d) Λ ¬e          )   ([ a,b,c,e,   f   F   d      ],   491)

         
加QQ：99515681  WX：codinghelp  Email: 99515681@qq.com
