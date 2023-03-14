theory Thm7AVL
imports
  "Thm7"
  "HOL-Data_Structures.AVL_Set"
begin

section "Strongly Joinable AVL Trees"

subsection "Join for AVL Trees"

fun joinR where
"joinR L a R = (case L of Node l (k,_) r \<Rightarrow> 
 if ht r \<le> ht R + 1 
 then balR l k (node r a R)
 else balR l k (joinR r a R))"

declare joinR.simps[simp del]

fun joinL where
"joinL L a R = (case R of Node l (k,_) r \<Rightarrow> 
 if ht l \<le> ht L + 1 
 then balL (node L a l) k r
 else balL (joinL L a l) k r)"

declare joinL.simps[simp del]

fun join where 
"join l a r = 
(if      ht l > ht r + 1 then joinR l a r
 else if ht r > ht l + 1 then joinL l a r
 else    node l a r)"


subsection "Proof of Correctness"
subsubsection "Set Preservation"

lemma balR_set:"set_tree (balR l a r) = set_tree 
  l \<union> {a} \<union> set_tree r"
  by (auto simp: balR_def node_def split!: if_splits tree.splits)

lemma joinR_set:"ht l > ht r + 1 \<Longrightarrow> set_tree (joinR l a r) = set_tree 
  l \<union> {a} \<union> set_tree r"
proof(induction l a r rule: joinR.induct)
  case (1 L a R)
  then show ?case 
    by (auto simp: joinR.simps[of L a R] balR_set node_def split!: if_splits tree.splits)
qed

lemma balL_set:"set_tree (balL l a r) = set_tree 
  l \<union> {a} \<union> set_tree r"
  by (auto simp: balL_def node_def split!: if_splits tree.splits)

lemma joinL_set:"ht r > ht l + 1 \<Longrightarrow> set_tree (joinL l a r) = set_tree 
  l \<union> {a} \<union> set_tree r"
proof(induction l a r rule: joinL.induct)
  case (1 L a R)
  then show ?case 
    by (auto simp: joinL.simps[of L a R]  balL_set node_def split!: if_splits tree.splits)
qed

corollary set_join:"set_tree (join l a r) = set_tree l \<union> {a} \<union> set_tree r"
  by(auto simp: node_def joinR_set joinL_set split!: if_splits)

subsubsection "BST Preservation"

lemma balR_bst:"\<lbrakk>bst l; bst r; \<forall>x\<in>set_tree l. x < a; \<forall>y\<in>set_tree r. a < y\<rbrakk>
  \<Longrightarrow> bst (balR l a r)"
  by (auto simp: balR_def node_def split!: if_splits tree.splits)

lemma joinR_bst:"\<lbrakk>ht l > ht r + 1; bst l; bst r; \<forall>x\<in>set_tree l. x < a; \<forall>y\<in>set_tree r. a < y\<rbrakk>
  \<Longrightarrow> bst (joinR l a r)"
proof(induction l a r arbitrary: b rule: joinR.induct)
  case (1 L a R)
  then show ?case
    by (auto simp: joinR.simps[of L a R] node_def balR_bst joinR_set ball_Un 
      intro!: balR_bst split!: if_splits tree.splits) 
qed

lemma balL_bst:"\<lbrakk>bst l; bst r; \<forall>x\<in>set_tree l. x < a; \<forall>y\<in>set_tree r. a < y\<rbrakk>
  \<Longrightarrow> bst (balL l a r)"
  by (auto simp: balL_def node_def split!: if_splits tree.splits)

lemma joinL_bst:"\<lbrakk>ht r > ht l + 1; bst l; bst r; \<forall>x\<in>set_tree l. x < a; \<forall>y\<in>set_tree r. a < y\<rbrakk>
\<Longrightarrow> bst (joinL l a r)"
proof(induction l a r arbitrary: b rule: joinL.induct)
  case (1 L a R)
  then show ?case
    by (auto simp: joinL.simps[of L a R] node_def balL_bst joinL_set ball_Un 
      intro!: balL_bst split!: if_splits tree.splits) 
qed

corollary bst_join:"bst (Node l (a, b) r) \<Longrightarrow> bst (join l a r)"
  by(auto simp: node_def joinR_bst joinL_bst split!: if_splits)

subsubsection "Preservation of AVL Predicate"
text\<open>Automatic proofs are relatively expensive in this section, expect a few minutes
runtime on low-powered machines.\<close>

lemma avl_joinR_height:"\<lbrakk>avl l; avl r; height l > height r + 1\<rbrakk> 
\<Longrightarrow> avl (joinR l a r) \<and> height (joinR l a r) \<in> {height l, height l + 1}"
proof(induction l a r rule: joinR.induct)
  case (1 L a R)
  then show ?case 
    by(auto simp: joinR.simps[of L a R] balR_def node_def max_absorb2 split!: if_splits tree.splits)
    \<comment> \<open>6 subgoals\<close>
    fastforce+
qed

lemma avl_joinL_height:"\<lbrakk>avl l; avl r; height r > height l + 1\<rbrakk> 
\<Longrightarrow> avl (joinL l a r) \<and> height (joinL l a r) \<in> {height r, height r + 1}"
proof(induction l a r rule: joinL.induct)
  case (1 L a R)
  then show ?case 
    by(auto simp: joinL.simps[of L a R] balL_def node_def max_absorb2 split!: if_splits tree.splits)
    \<comment> \<open>20 subgoals\<close>
    fastforce+
qed

corollary inv_join:"\<lbrakk>avl l; avl r\<rbrakk> \<Longrightarrow> avl (join l a r)"
  by(auto simp: node_def avl_joinR_height avl_joinL_height split: if_splits)

text \<open>To finish the proof of functional correctness, instantiate the \<open>Set2_Join\<close> locale.\<close>

interpretation tree_ht: Set2_Join
where join = join and inv = avl
proof (standard, goal_cases)
  case 1 show ?case by (rule set_join)
next
  case 2 thus ?case by (rule bst_join)
next
  case 3 show ?case by simp
next
  case 4 thus ?case by (rule inv_join)
next
  case 5 thus ?case by simp
qed

subsection "Proof of Strongly Joinable Properties"


subsubsection "Monoticity Rule"

corollary join_height: 
assumes "avl l \<and> avl r"
shows "height (join l a r) \<in> {max (height l) (height r), max (height l) (height r) + 1}"
proof-
  consider 
    (Right) R  where "R = joinR l a r" and "ht l > ht r + 1" and 
                     "join l a r = R"
  | (Left)  L  where "L = joinL l a r" and "ht r > ht l + 1" and 
                     "join l a r = L"
  | (Node)  EQ where "EQ = node l a r" and "ht r \<le> ht l + 1" and 
                     "ht l \<le> ht r + 1" and "join l a r = EQ"
    by(auto split!: if_splits)linarith
  then show ?thesis
  proof cases
    case Right
    from this assms show ?thesis 
      by (metis avl_joinR_height ht_height linorder_not_less max_def trans_le_add1)
  next
    case Left
    from this assms show ?thesis 
      by (metis add_lessD1 ht_height avl_joinL_height max.absorb4)
  next
  next
    case Node
    then show ?thesis 
      by simp
  qed
qed

corollary rule_mono: "\<lbrakk>avl l; avl r\<rbrakk> \<Longrightarrow> max (height l) (height r) \<le> height (join l a r)"
  using join_height 
  by (metis insertE le_add_same_cancel1 zero_le_one nle_le singletonD)

subsubsection "Submodularity Rule"

corollary rule_sub_dec: 
assumes "height l' \<le> height l \<and> height r' \<le> height r"
assumes "avl l' \<and> avl r' \<and> avl (Node l (a,b) r)"
shows "height (join l' a r') \<le> height (Node l (a,b) r)"
proof-
  from assms have "max (height l') (height r') \<le> max (height l) (height r)"
    by linarith
  moreover from assms have "height (join l' a r') \<le> max (height l') (height r') + 1"
    using join_height by (metis order_eq_iff insertE singletonD trans_le_add1)
  moreover have "height (Node l (a,b) r) = max (height l) (height r) + 1"
    by simp
  ultimately show ?thesis 
    by linarith
qed


(* TODO maybe shorten this *)
lemma rule_sub_inc: 
assumes "height l \<le> height l' \<and> height r \<le> height r'"
assumes "height r' - height r \<le> x \<and> height l' - height l \<le> x"
assumes "avl l' \<and> avl r' \<and> avl (Node l (a,b) r)"
shows "height (Node l (a,b) r) \<le> height (join l' a r') \<and>
  height (join l' a r') - height (Node l (a,b) r) \<le> x"
proof-
    have joinmax:"height (join l' a r') \<le> max (height l') (height r') + 1"
      using assms join_height by (metis order_eq_iff insertE singletonD trans_le_add1)
    show ?thesis 
    proof(cases "height l \<ge> height r")
      case True
      then have "height (Node l (a,b) r) = height l + 1"
        using assms by simp
      moreover then have "max (height l') (height r') \<le> height l + x"
        using True assms by auto
      moreover then have "height (join l' a r') \<le> height l + x + 1"
        using assms joinmax by linarith 
      moreover have "height (join l' a r') \<noteq> height l"
        proof(rule ccontr)
          assume *:"\<not> height (join l' a r') \<noteq> height l"
          moreover then have heq:"height l = height l'"
            by (metis assms(1) assms(3) le_antisym max.bounded_iff rule_mono)
          ultimately have "height r' \<le> height l'"
            by (metis assms(3) max.commute max_def rule_mono)
          moreover then have "join l' a r' = node l' a r'"
            using heq assms by auto
          ultimately have "height (join l' a r') = height l + 1 "
            using heq by simp
          then show False 
            using * by linarith
          qed
      moreover have "height l \<le> height (join l' a r')"
        by (meson assms(1) assms(3) le_max_iff_disj order_trans rule_mono)
      ultimately show ?thesis 
        by linarith
    next
      case False
      then have "height (Node l (a,b) r) = height r + 1"
        using assms by simp
      moreover then have "max (height l') (height r') \<le> height r + x"
        using False assms by auto
      moreover then have "height (join l' a r') \<le> height r + x + 1"
        using assms joinmax by linarith 
      moreover have "height (join l' a r') \<noteq> height r"
        proof(rule ccontr)
          assume *:"\<not> height (join l' a r') \<noteq> height r"
          moreover then have heq:"height r = height r'"
            by (metis assms(1) assms(3) le_antisym max.bounded_iff rule_mono)
          ultimately have "height l' \<le> height r'"
            by (metis assms(3) max_def rule_mono)
          moreover then have "join l' a r' = node l' a r'"
            using heq assms by auto
          ultimately have "height (join l' a r') = height r + 1 "
            using heq by simp
          then show False 
            using * by linarith
          qed
      moreover have "height r \<le> height (join l' a r')"
        by (meson assms(1) assms(3) le_max_iff_disj order_trans rule_mono)
      ultimately show ?thesis 
        by linarith
    qed
qed

subsubsection "Balancing Rule" 

lemma rule_bal: "avl t \<Longrightarrow> bal t height 1 2"
  by(induction t) auto

subsubsection "Cost Rule"

fun T_joinR :: "'a tree_ht \<Rightarrow> 'a \<Rightarrow> 'a tree_ht \<Rightarrow> nat" where
"T_joinR L a R = (case L of Node l (k,_) r \<Rightarrow> 
 if ht r \<le> ht R + 1 
 then 1 
 else 1 + T_joinR r a R)"

declare T_joinR.simps[simp del]

fun T_joinL :: "'a tree_ht \<Rightarrow> 'a \<Rightarrow> 'a tree_ht \<Rightarrow> nat" where
"T_joinL L a R = (case R of Node l (k,_) r \<Rightarrow> 
 if ht l \<le> ht L + 1 
 then 1 
 else 1 + T_joinL L a l)"

declare T_joinL.simps[simp del]

fun T_join :: "'a tree_ht \<Rightarrow> 'a \<Rightarrow> 'a tree_ht \<Rightarrow> nat" where 
"T_join l a r = 
(if      ht l > ht r + 1 then T_joinR l a r
 else if ht r > ht l + 1 then T_joinL l a r
 else    1)"

lemma T_joinR:"\<lbrakk>avl l; avl r; ht l > ht r + 1\<rbrakk> \<Longrightarrow> T_joinR l a r \<le> 1 + height l - height r"
proof(induction l a r rule: T_joinR.induct)
  case (1 L a R)
  then show ?case 
    using T_joinR.simps[of L a R]
    by(auto simp: max_absorb2 split!: if_splits tree.splits) fastforce
qed

lemma T_joinL:"\<lbrakk>avl l; avl r; ht r > ht l + 1\<rbrakk> \<Longrightarrow> T_joinL l a r \<le> 1 + height r - height l"
proof(induction l a r rule: T_joinL.induct)
  case (1 L a R)
  then show ?case 
    by(auto simp: T_joinL.simps[of L a R] max_absorb1 split!: if_splits tree.splits) fastforce
qed

corollary rule_cost:
assumes "avl l \<and> avl r" 
shows "T_join l a r \<le> 1 + nat(abs(int(height l) - int(height r)))"
proof-
  consider 
    (Right) R where "R = T_joinR l a r" and "ht l > ht r + 1" and 
                    "T_join l a r = R"
  | (Left)  L where "L = T_joinL l a r" and "ht r > ht l + 1" and 
                    "T_join l a r = L"
  | (Node)  EQ where "EQ = 1" and "ht r \<le> ht l + 1" and 
                     "ht l \<le> ht r + 1" and "T_join l a r = EQ"
    by(auto split!: if_splits)linarith
  then show ?thesis 
  proof cases
    case Right
    then have "max (height l) (height r) = height l"
      using assms by simp
    then moreover have "nat(abs(int(height l) - int(height r))) = height l - height r"
      by simp
    ultimately show ?thesis 
      using Right T_joinR assms by (metis Nat.add_diff_assoc max.orderI)
  next
    case Left
    then have "max (height l) (height r) = height r"
      using assms by simp
    then moreover have "nat(abs(int(height l) - int(height r))) = height r - height l"
      by simp
    ultimately show ?thesis 
      using Left T_joinL assms by (metis Nat.add_diff_assoc max.cobounded1)
  next
    case Node
    then show ?thesis 
      by simp
  qed
qed

interpretation tree_ht: StronglyJoinable
where join = join and inv = avl
and rank = height and c\<^sub>l = 1 and c\<^sub>u = 2
proof (standard, goal_cases)
  case 1 thus ?case by simp
next
  case (2 l r a) thus ?case by (metis of_nat_le_iff of_nat_max rule_mono)
next
  \<comment> \<open>this simply converts from nat to real, but takes a long time to run, expect a few minutes\<close>
  case (3 l' l r' r x a b) 
  then show ?case 
    by (smt (verit) diff_diff_cancel diff_le_self le_diff_iff' nat_le_linear of_nat_diff of_nat_le_iff of_nat_mono ord_le_eq_subst rule_sub_inc) 
next
  case (4 l' l r' r a b) thus ?case 
    by (meson of_nat_le_iff rule_sub_dec)
next
  case 5 thus ?case by simp
next
  case (6 t) thus ?case by(rule rule_bal)
qed

end