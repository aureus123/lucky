theory ACN_Chromatic
  imports ACN_Basics "Girth_Chromatic.Ugraphs"
begin

section \<open>The chromatic number agrees with the AFP entry Girth Chromatic\<close>

text \<open>
  L. Noschinski's graphs (\<^emph>\<open>Girth Chromatic\<close>) have natural vertices: a @{typ ugraph} is a pair
  \<open>(V, E)\<close>. A well-formed one with finitely many vertices is a @{locale fin_sgraph}, and on such a
  graph @{const fin_sgraph.chi} is his @{const chromatic_number}.
\<close>

lemma uwellformed_fin_sgraph:
  assumes "uwellformed (V, E)" "finite V"
  shows "fin_sgraph V E"
  using assms by unfold_locales (auto simp: uwellformed_def)

lemma chi_eq_chromatic_number:
  fixes V :: "nat set"
  assumes "fin_sgraph V E"
  shows "fin_sgraph.chi V E = chromatic_number (V, E)"
proof -
  interpret fin_sgraph V E by fact
  show ?thesis
    unfolding chi_def vertex_colorings_def chromatic_number_def Ugraphs.vertex_colorings_def by simp
qed

end
