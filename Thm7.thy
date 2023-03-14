theory Thm7
imports
  Complex_Main
  "HOL-Data_Structures.Set2_Join"
begin
text \<open>The following is a formalisation of strongly joinable trees as defined
in @{cite paper_main}.\<close>

section "StronglyJoinable Locale"

fun bal :: "('a * 'b) tree \<Rightarrow> (('a * 'b) tree \<Rightarrow> real) 
      \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
"bal Leaf _ _ _ = True" |
"bal (Node l a r) rank c\<^sub>l c\<^sub>u = 
  (max (rank l) (rank r) + c\<^sub>l \<le> rank (Node l a r) \<and> 
   min (rank l) (rank r) + c\<^sub>u \<ge> rank (Node l a r) \<and> 
   bal l rank c\<^sub>l c\<^sub>u \<and> bal r rank c\<^sub>l c\<^sub>u )"

locale StronglyJoinable = Set2_Join +
fixes rank :: "('a * 'b) tree \<Rightarrow> real"
fixes c\<^sub>l c\<^sub>u :: real

assumes rule_empty: "rank Leaf = 0"
assumes rule_mono: "\<lbrakk>inv l; inv r\<rbrakk> \<Longrightarrow> max (rank l) (rank r) \<le> rank (join l a r)"
assumes rule_sub_inc: "\<lbrakk>rank l \<le> rank l'; rank r \<le> rank r'; rank r' - rank r \<le> x; rank l' - rank l \<le> x;
  inv l'; inv r'; inv (Node l (a,b) r)\<rbrakk> \<Longrightarrow> 
  rank (Node l (a,b) r) \<le> rank (join l' a r') \<and>
  rank (join l' a r') - rank (Node l (a,b) r) \<le> x"
  
assumes rule_sub_dec: "\<lbrakk>rank l' \<le> rank l; rank r' \<le> rank r; 
  inv l'; inv r'; inv (Node l (a,b) r)\<rbrakk> \<Longrightarrow> 
  rank (join l' a r') \<le> rank (Node l (a,b) r)"
assumes c_vals:"0 \<le> c\<^sub>l \<and> c\<^sub>l \<le> 1 \<and> c\<^sub>u \<ge> 1"
assumes rule_bal:"inv t \<Longrightarrow> bal t rank c\<^sub>l c\<^sub>u"
begin

\<comment> \<open>directly define a timing function for @{term join}\<close>
definition T_join :: "('a * 'b) tree \<Rightarrow> 'a \<Rightarrow> ('a * 'b) tree \<Rightarrow> real" where
"T_join l a r = abs(rank l - rank r)"

subsection "Auxiliary Properties"

definition "balanced t = bal t rank c\<^sub>l c\<^sub>u"

lemma rank_mono:"\<lbrakk>t = (Node l a r); balanced t\<rbrakk> \<Longrightarrow> rank t \<ge> rank l \<and> rank t \<ge> rank r"
  using balanced_def c_vals by force

definition "c\<^sub>\<delta> = c\<^sub>u - c\<^sub>l"

lemma dmax:"balanced (Node l a r) \<Longrightarrow> abs(rank l - rank r) \<le> c\<^sub>\<delta>"
  using balanced_def c\<^sub>\<delta>_def by force

lemma rank_pos:"balanced t \<Longrightarrow> rank t \<ge> 0"
  unfolding balanced_def apply(induction t)
  apply(auto simp add: c_vals rule_empty)
  using c_vals by linarith  

lemma height_rank:"balanced t \<Longrightarrow> rank t \<le> c\<^sub>u * height t"
unfolding balanced_def
proof(induction t)
  case Leaf
  then show ?case 
    by (simp add: rule_empty)
next
  case (Node l a r)
  then have "rank l \<le> c\<^sub>u * height l"
    by simp
  moreover have "rank r \<le> c\<^sub>u * height r"
    using Node by simp
  ultimately have "max (rank l) (rank r) \<le> c\<^sub>u * max (height l) (height r)"
    by (smt (verit, best) c_vals max.cobounded1 max.cobounded2 mult_mono of_nat_0_le_iff of_nat_mono)
  then have "max (rank l) (rank r) + c\<^sub>u \<le> c\<^sub>u * max (height l) (height r) + c\<^sub>u"
    using c_vals by argo
  also have "... \<le> c\<^sub>u * (max (height l) (height r) + 1)"
    using c_vals by (simp add: distrib_left)
  also have "... \<le> c\<^sub>u * height (Node l a r)"
    using c_vals by auto
  finally show ?case 
    using Node by auto
qed

subsection "Splitting the @{emph \<open>split\<close>}"
fun splitl :: "('a * 'b) tree \<Rightarrow> 'a \<Rightarrow> ('a * 'b) tree" where
"splitl Leaf x = Leaf" |
"splitl (Node l (a,_) r) x = (case (cmp x a) of
   LT \<Rightarrow> splitl l x |
   EQ \<Rightarrow> l |
   GT \<Rightarrow> join l a (splitl r x))"

fun splitr :: "('a * 'b) tree \<Rightarrow> 'a \<Rightarrow> ('a * 'b) tree" where
"splitr Leaf x = Leaf" |
"splitr (Node l (a, _) r) x = (case (cmp x a) of
   LT \<Rightarrow> join (splitr l x) a r |
   EQ \<Rightarrow> r |
   GT \<Rightarrow> splitr r x)"

lemma splitl_eq_l:"split t x = (l,b,r) \<Longrightarrow> splitl t x = l"
  by(induction t arbitrary: l b r)(auto simp: split.simps split!: prod.splits)
  
lemma splitr_eq_r:"split t x = (l,b,r) \<Longrightarrow> splitr t x = r"
  by(induction t arbitrary: l b r)(auto simp: split.simps split!: prod.splits)

corollary inv_splitl:"inv t \<Longrightarrow> inv (splitl t x)"
  by (metis split_inv splitl_eq_l prod_cases3)

corollary inv_splitr:"inv t \<Longrightarrow> inv (splitr t x)"
  by (metis split_inv splitr_eq_r prod_cases3)

subsection "Bounding the StronglyJoinable Results"

lemma splitl_rank:"inv t \<Longrightarrow> rank t \<ge> rank (splitl t x)"
proof(induction t rule: tree2_induct)
  case Leaf
  then show ?case 
    by simp
next
  case (Node l a b r)
  then have t_bal:"balanced (Node l (a,b) r)"
    using rule_bal balanced_def by fast

  then show ?case 
  proof(cases "cmp x a")
    case LT
    then have "rank l \<ge> rank (splitl l x)"
      using Node inv_Node by blast
    then show ?thesis 
      using Node t_bal LT balanced_def c_vals by auto
  next
    case EQ
    then show ?thesis 
      using Node t_bal balanced_def c_vals by auto
  next
    case GT
    then have *:"splitl (Node l (a,b) r) x = join l a (splitl r x)"
      by simp
    
    \<comment> \<open>from the IH\<close>
    have "rank r \<ge> rank (splitl r x)"
      using Node inv_Node by blast
    \<comment> \<open>trivially\<close>
    moreover have "rank l \<ge> rank l"
      by simp
    \<comment> \<open>from the submodularity rule\<close>
    ultimately have "rank (Node l (a,b) r) \<ge> rank (join l a (splitl r x))"
      by (meson Node.prems inv_Node rule_sub_dec inv_splitl)
    then show ?thesis 
      using * by simp
  qed
qed

lemma splitr_rank:"inv t \<Longrightarrow> rank t \<ge> rank (splitr t x)"
proof(induction t rule: tree2_induct)
  case Leaf
  then show ?case 
    by simp
next
  case (Node l a b r)
  then have t_bal:"balanced (Node l (a,b) r)"
    using rule_bal balanced_def by fast

  then show ?case 
  proof(cases "cmp x a")
    case LT
    have "rank l \<ge> rank (splitr l x)"
      using Node inv_Node by blast
    moreover have "rank r \<ge> rank r"
      by simp
    ultimately have "rank (Node l (a,b) r) \<ge> rank (join (splitr l x) a r)"
      by (meson Node.prems inv_Node rule_sub_dec inv_splitr)
    then show ?thesis 
      using LT by simp
  next
    case EQ
    then show ?thesis 
      using Node t_bal balanced_def c_vals by force
  next
    case GT
    then have "rank r \<ge> rank (splitr r x)"
      using Node inv_Node by blast
    then show ?thesis 
      using Node t_bal GT balanced_def c_vals by auto
  qed
qed

corollary split_rank: "\<lbrakk>split t x = (l,b,r); inv t\<rbrakk> \<Longrightarrow> rank l \<le> rank t \<and> rank r \<le> rank t"
  using splitl_eq_l splitl_rank splitr_eq_r splitr_rank by blast

subsection "Timing Functions"

fun T_split :: "('a * 'b) tree \<Rightarrow> 'a \<Rightarrow> real" where
"T_split Leaf x = 1" |
"T_split (Node l (a,_) r) x = (case (cmp x a) of
   LT \<Rightarrow> let (l1,_,l2) = split l x in 1 + T_join l2 a r + T_split l x |
   EQ \<Rightarrow> 1 |
   GT \<Rightarrow> let (r1,_,r2) = split r x in 1 + T_join l a r1 + T_split r x)"

fun T_splitl :: "('a * 'b) tree \<Rightarrow> 'a \<Rightarrow> real" where
"T_splitl Leaf x = 1" |
"T_splitl (Node l (a,_) r) x = (case (cmp x a) of
   LT \<Rightarrow> T_splitl l x |
   EQ \<Rightarrow> 1 |
   GT \<Rightarrow> 1 + T_join l a (splitl r x) + T_splitl r x)"

fun T_splitr :: "('a * 'b) tree \<Rightarrow> 'a \<Rightarrow> real" where
"T_splitr Leaf x = 1" |
"T_splitr (Node l (a,_) r) x = (case (cmp x a) of
   LT \<Rightarrow> 1 + T_join (splitr l x) a r + T_splitr l x |
   EQ \<Rightarrow> 1 |
   GT \<Rightarrow> T_splitr r x)"

lemma T_split_lr:"T_split t x \<le> T_splitl t x + T_splitr t x"
proof(induction t rule: tree2_induct)
  case Leaf
  then show ?case 
    by simp
next
  case (Node l a b r)
  let ?t = "Node l (a, b) r"

  show ?case 
  proof(cases "cmp x a")
    case LT
    then consider (Left) l1 c l2 where "(l1,c,l2) = split l x" and "x < a" 
      and "T_split ?t x = 1 + T_join l2 a r + T_split l x"
      and "T_splitl ?t x = T_splitl l x"
      and "T_splitr ?t x = 1 + T_join (splitr l x) a r + T_splitr l x"
      by(auto split: prod.splits)
        (metis (no_types, lifting) prod.exhaust_sel split_beta)
    
    then show ?thesis 
      proof cases
        case Left
        have "splitr l x = l2" 
          using Left splitr_eq_r by metis
        then show ?thesis 
          using Left Node by auto
      qed
  next
    case EQ
    then show ?thesis 
      by simp
  next
    case GT
    then consider (Right) r1 c r2 where "(r1,c,r2) = split r x" and "x > a" 
      and "T_split ?t x = 1 + T_join l a r1 + T_split r x"
      and "T_splitl ?t x = 1 + T_join l a (splitl r x) + T_splitl r x"
      and "T_splitr ?t x = T_splitr r x"
      by(auto split: prod.splits)
        (metis (no_types, lifting) prod.exhaust_sel split_beta)

    then show ?thesis 
      proof cases
        case Right
        have "splitl r x = r1" 
          using Right splitl_eq_l by metis
        then show ?thesis 
          using Right Node by auto
      qed
  qed
qed

subsection "Bounding the Timing Functions"

definition "c\<^sub>1 = 2 * c\<^sub>\<delta> + 1"

lemma c1_pos:"c\<^sub>1 > 0"
  using c\<^sub>1_def c\<^sub>\<delta>_def c_vals by linarith

lemma hnode_r:"c\<^sub>1 * height r \<le> c\<^sub>1 * height (Node l a r) - c\<^sub>1"
proof-
  have "height (Node l a r) \<ge> height r + 1"
    by simp
  then have "c\<^sub>1 * height (Node l a r) \<ge> c\<^sub>1 * (height r + 1)"
    using c1_pos by simp
  then have "c\<^sub>1 * height (Node l a r) \<ge> c\<^sub>1 * (height r) + c\<^sub>1"
    using c1_pos by (simp add: distrib_left)
  then show ?thesis 
    by simp
qed


lemma T_splitl_bounded:
"inv t \<Longrightarrow> T_splitl t x \<le> 1 + c\<^sub>1 * height t + rank (splitl t x)"
proof(induction t rule: tree2_induct)
  case Leaf
  then show ?case 
    by (simp add: rule_empty)
next
  case (Node l a b r)
  let ?t = "(Node l (a,b) r)"

  have t_bal:"balanced ?t"
    using rule_bal Node balanced_def by fast
  
  have inv_subtrees:"inv l \<and> inv r"
    using Node inv_Node by blast
  show ?case 
  proof(cases "cmp x a")
    case LT
    \<comment> \<open>follows directly from the IH\<close>
    have *:"height l \<le> height ?t"
      by simp
    have "T_splitl ?t x \<le> 1 + c\<^sub>1 * height l + rank (splitl ?t x)"
      using LT Node inv_subtrees by force
    also have "... \<le> 1 + c\<^sub>1 * height ?t + rank (splitl ?t x)"
      using c1_pos by simp
    finally show ?thesis .
  next
    case EQ
    then show ?thesis 
      using balanced_def c1_pos inv_subtrees rank_pos rule_bal by auto 
  next
    case GT
    \<comment> \<open>since the rank of the split result is bounded\<close>
    have "rank r \<ge> rank (splitl r x)"
      using Node splitl_rank inv_subtrees by blast
    \<comment> \<open>and the tree is balanced\<close>
    then have "rank l + c\<^sub>\<delta> \<ge> rank (splitl r x)"
      using Node balanced_def t_bal c\<^sub>\<delta>_def by force
    \<comment> \<open>there must be some \<open>\<delta>\<close> that satisfies the equation below\<close>
    moreover then obtain \<delta> where hdiff:"rank l + c\<^sub>\<delta> = rank (splitl r x) + \<delta>"
      by (metis add.commute diff_add_cancel)
    \<comment> \<open>thus the time to join is bounded\<close>
    ultimately have "T_join l a (splitl r x) \<le> c\<^sub>\<delta> + \<delta>"
      using T_join_def c\<^sub>\<delta>_def c_vals by force
    \<comment> \<open>since \<open>x > a\<close>\<close>
    moreover have "T_splitl ?t x \<le> 1 + T_join l a (splitl r x) + T_splitl r x"
      using GT by simp
    \<comment> \<open>plugging in the bound for \<open>T_join l a (splitl r x)\<close>\<close>
    ultimately have "T_splitl ?t x \<le> 1 + c\<^sub>\<delta> + \<delta> + T_splitl r x"
      by simp
    \<comment> \<open>applying the induction hypothesis\<close>
    then have "T_splitl ?t x \<le> 1 + c\<^sub>\<delta> + \<delta> + 1 + c\<^sub>1 * height r + rank (splitl r x)"
      using Node inv_subtrees by fastforce
    \<comment> \<open>expressing @{term "rank (splitl t x)"} in terms of @{term "rank l + c\<^sub>\<delta>"} and @{term \<delta>}\<close>
    also have "... \<le> 1 + c\<^sub>\<delta> + \<delta> + 1 + c\<^sub>1 * height r + rank l + c\<^sub>\<delta> - \<delta>"
      using hdiff by simp
    \<comment> \<open>simplifying the expression\<close>
    also have "... \<le> 2 + 2*c\<^sub>\<delta> + c\<^sub>1 * height r + rank l"
      by simp
    \<comment> \<open>from the monoticity rule\<close>
    also have "... \<le> 2 + 2*c\<^sub>\<delta> + c\<^sub>1 * height r + rank (splitl ?t x)"
      using inv_subtrees inv_splitl rule_mono inv_subtrees GT by fastforce
    \<comment> \<open>from the definition of height\<close>
    also have "... \<le> 2 + 2*c\<^sub>\<delta> + c\<^sub>1 * height ?t - c\<^sub>1 + rank (splitl ?t x)"
      using hnode_r by auto
    \<comment> \<open>finally, because @{term "c\<^sub>1 = 2 * c\<^sub>\<delta> + 1"}\<close>
    also have "... \<le> 1 + c\<^sub>1 * height ?t + rank (splitl ?t x)"
      by (simp add: c\<^sub>1_def)
    finally show ?thesis .
  qed
qed

lemma hnode_l:"c\<^sub>1 * height l \<le> c\<^sub>1 * height (Node l a r) - c\<^sub>1"
proof-
  have "height (Node l a r) \<ge> height l + 1"
    by simp
  then have "c\<^sub>1 * height (Node l a r) \<ge> c\<^sub>1 * (height l + 1)"
    using c1_pos by simp
  then have "c\<^sub>1 * height (Node l a r) \<ge> c\<^sub>1 * (height l) + c\<^sub>1"
    using c1_pos by (simp add: distrib_left)
  then show ?thesis 
    by simp
qed

lemma T_splitr_bounded:
"inv t \<Longrightarrow> T_splitr t x \<le> 1 + c\<^sub>1 * height t + rank (splitr t x)"
proof(induction t rule: tree2_induct)
  case Leaf
  then show ?case 
    by (simp add: rule_empty)
next
  case (Node l a b r)
  let ?t = "(Node l (a,b) r)"

  have t_bal:"balanced ?t"
    using rule_bal Node balanced_def by fast
  
  have inv_subtrees:"inv l \<and> inv r"
    using Node inv_Node by blast
  show ?case 
  proof(cases "cmp x a")
    case LT
    have "rank l \<ge> rank (splitr l x)"
      using Node splitr_rank inv_subtrees by blast
    then have "rank r + c\<^sub>\<delta> \<ge> rank (splitr l x)"
      using Node balanced_def t_bal c\<^sub>\<delta>_def by force
    then obtain \<delta> where hdiff:"rank r + c\<^sub>\<delta> = rank (splitr l x) + \<delta>"
      by (metis add.commute diff_add_cancel)
    then have "T_join (splitr l x) a r \<le> c\<^sub>\<delta> + \<delta>"
      using T_join_def hdiff using \<open>rank (splitr l x) \<le> rank r + c\<^sub>\<delta>\<close> c\<^sub>\<delta>_def c_vals by force
    then have "T_splitr ?t x \<le> 1 + c\<^sub>\<delta> + \<delta> + 1 + c\<^sub>1 * height l + rank (splitr l x)"
      using Node LT inv_subtrees by fastforce
    also have "... \<le> 1 + c\<^sub>\<delta> + \<delta> + 1 + c\<^sub>1 * height l + rank r + c\<^sub>\<delta> - \<delta>"
      using hdiff by simp
    also have "... \<le> 2 + 2*c\<^sub>\<delta>  + c\<^sub>1 * height l + rank r"
      by simp
    also have "... \<le> 2 + 2*c\<^sub>\<delta> + c\<^sub>1 * height l + rank (splitr ?t x)"
      using inv_subtrees inv_splitr rule_mono inv_subtrees LT by fastforce
    also have "... \<le> 2 + 2*c\<^sub>\<delta> + c\<^sub>1 * height ?t - c\<^sub>1 + rank (splitr ?t x)"
      using hnode_l by auto
    finally show ?thesis 
      by (simp add: c\<^sub>1_def)
  next
    case EQ
    then show ?thesis 
      using balanced_def c1_pos inv_subtrees rank_pos rule_bal by auto
  next
    case GT
    have *:"height r \<le> height ?t"
      by simp
    have "T_splitr ?t x \<le> 1 + c\<^sub>1 * height r + rank (splitr ?t x)"
      using GT Node inv_subtrees by auto
    also have "... \<le> 1 + c\<^sub>1 * height ?t + rank (splitr ?t x)"
      by (simp add: c1_pos)
    finally show ?thesis .
  qed
qed

corollary T_splitl_ht:"inv t \<Longrightarrow> T_splitl t x \<le> 1 + (c\<^sub>1 + c\<^sub>u) * height t"
proof-
  assume assm:"inv t"

  then have "T_splitl t x \<le> 1 + c\<^sub>1 * height t + rank (splitl t x)"
    using T_splitl_bounded by simp
  also have "... \<le> 1 + c\<^sub>1 * height t + rank t"
    using assm splitl_rank by simp
  also have "... \<le> 1 + c\<^sub>1 * height t + c\<^sub>u * height t"
     by (simp add: assm balanced_def height_rank rule_bal)
  also have "... \<le> 1 + (c\<^sub>1 + c\<^sub>u) * height t"
    by argo
  finally show ?thesis .
qed

corollary T_splitr_ht:"inv t \<Longrightarrow> T_splitr t x \<le> 1 + (c\<^sub>1 + c\<^sub>u) * height t"
proof-
  assume assm:"inv t"

  then have "T_splitr t x \<le> 1 + c\<^sub>1 * height t + rank (splitr t x)"
    using T_splitr_bounded by simp
  also have "... \<le> 1 + c\<^sub>1 * height t + rank t"
    using assm splitr_rank by simp
  also have "... \<le> 1 + c\<^sub>1 * height t + c\<^sub>u * height t"
     by (simp add: assm balanced_def height_rank rule_bal)
  also have "... \<le> 1 + (c\<^sub>1 + c\<^sub>u) * height t"
    by argo
  finally show ?thesis .
qed

subsection "Proof of Main Theorem"

theorem T_split_bounded: 
assumes "inv t"
shows "T_split t x \<le> 2 + 2 * (c\<^sub>1 + c\<^sub>u) * height t"
proof-
  have "T_split t x \<le> T_splitl t x + T_splitr t x"
    using T_split_lr by blast
  also have "... \<le> 1 + (c\<^sub>1 + c\<^sub>u) * height t + 1 + (c\<^sub>1 + c\<^sub>u) * height t"
    using assms T_splitl_ht T_splitr_ht by (smt (verit, best))
  also have "... \<le> 2 + 2 * (c\<^sub>1 + c\<^sub>u) * height t"
    by linarith
  finally show ?thesis .
qed

end
end