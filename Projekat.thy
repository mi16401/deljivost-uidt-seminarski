theory Projekat
  imports Main
begin

(*ZADATAK: *)
(*Ako su a i b prosti brojevi veci od 3 i a>b dokazati da je proizvod (a+b)(a-b) deljiv sa 12*)


(*definicija PROSTOG BROJA*)

definition prost :: "nat \<Rightarrow> bool"  where
 "prost x \<longleftrightarrow> 1 < x \<and> (\<forall>a \<in> {1..x}. a dvd x \<longrightarrow>  a = 1 \<or> a = x)"

(*provera definicije prostog broja*)
value "prost 5"
value "prost 12"
value "prost 113"

(*Broj je deljiv sa 3 ako mu je zbir cifara deljiv sa 3*)
(*potrebna nam je funkcija koja pravi listu cifara*)
fun izdvoj_cifre :: "nat \<Rightarrow> nat list" where 
  "izdvoj_cifre x =  (if x \<le> 9 then [x] 
      else x mod 10 # izdvoj_cifre (x div 10))"

value "izdvoj_cifre 123"

(*racunamo sumu cifara*)
abbreviation suma :: "nat \<Rightarrow> nat" where
  "suma x \<equiv> sum_list (izdvoj_cifre x)"

value "suma 245"

(*DELJIV SA 3*)
definition deljiv_3 ::"nat\<Rightarrow>bool" where
"deljiv_3 x = ( if (suma x mod 3 = 0) then True else False ) "

(*provera*)
value "deljiv_3 12"
value "deljiv_3 5"
value "deljiv_3 531840" 

(*Broj je deljiv sa 4 ako mu je dvocifreni zavrsetak deljiv sa 4*)
(*ova funkcija nam ne treba za nepraznu listu jer nam ona nista ne govori-ne postoji br bez cifara*)
fun dvocifren_broj:: "nat list \<Rightarrow> nat" where 
"dvocifren_broj [x] = x" | (*slucaj jednocifrenih brojeva*)
"dvocifren_broj (x # y # xs) = x + 10*y"

(*spajamo sve da ne bismo pisali kompoziciju funkcija*)
definition dvocifren_zavrsetak:: "nat \<Rightarrow> nat" where
"dvocifren_zavrsetak x = dvocifren_broj(izdvoj_cifre x)"

lemma dvocifre_zavrsetak_bez_liste:
  assumes "x \<ge> 9"
  shows "dvocifren_zavrsetak x = (x mod 10) + 10 * ((x div 10) mod 10)"
  using assms
  unfolding dvocifren_zavrsetak_def
  by simp

(*DELJIV SA 4*)
definition deljiv_4 :: "nat \<Rightarrow> bool" where
"deljiv_4 x \<equiv> dvocifren_zavrsetak x mod 4 = 0"

value "deljiv_4 4"
value "deljiv_4 5450328"
value "deljiv_4 15"

(*DELJIV SA 12*)
(*Broj je deljiv brojem 12 ako je deljiv brojem 3 i brojem 4*)
definition deljiv_12 ::"nat\<Rightarrow>bool" where
"deljiv_12 x \<equiv> deljiv_3 x \<and> deljiv_4 x"

(*provera*)
value "deljiv_12 144"
value "deljiv_12 8030472"

(*dokaz leme o deljivosti broja sa 3*)
declare izdvoj_cifre.simps [simp del]

(****************************************vise nije tema rada***************************************)
(*osim dole definisane leme za deljivost sa 4*)
lemma suma_cifara_manja:
  shows "suma x \<le> x"
proof (induction x rule:izdvoj_cifre.induct)
  case (1 x)
  show ?case
  proof (cases "x \<le> 9")
    case True
    thus ?thesis
      by (simp add:izdvoj_cifre.simps)
  next
    case False
    thus ?thesis
      using 1
      by (simp add: izdvoj_cifre.simps[of x])
  qed
qed

lemma dvd_9_suma_cifara:
 shows "3 dvd x \<longleftrightarrow> 3 dvd suma x"
 proof-
  have "suma x \<le> x"
    by (rule suma_cifara_manja)
  moreover
  have "3 dvd (x - suma x)"
  proof (induct x rule:izdvoj_cifre.induct)
    case (1 x)
    show ?case
    proof (cases "x \<le> 9")
      case True
      thus ?thesis
        by (simp add:izdvoj_cifre.simps)
    next
      case False
      have "x = 10 * (x div 10) + x mod 10"
        by simp
      hence "x - suma x = 10*(x div 10) - suma (x div 10)"
        using izdvoj_cifre.simps[of x] `\<not> x \<le> 9`
        by (metis add_diff_cancel_right' diff_diff_left sum_list.Cons)
      hence "x - suma x = 9*(x div 10) + (x div 10 - suma (x div 10))"
        using suma_cifara_manja[of "x div 10"]
        by auto
      thus ?thesis
        using 1 `\<not> x \<le> 9`
        by simp
    qed
  qed
  ultimately
  show ?thesis
    using dvd_diffD dvd_diffD1
    by blast
qed

(*GLAVNA TEOREMA KOJU DOKAZUJEMO - otprilike pomocne leme koje ce nam trebati*)

(*1:  Prosti brojevi veci od 3 su neparni pa su a i b neparni. 
  2:  Njihov zbir a+b i njihova razlika a-b su parni pa je i proizvod paran deljiv sa 4. 
  3:  Pri deljenju sa brojem 3 brojevi a i b mogu imati ostatak 1 ili 2. 
  4: Ako je ostatak isti onda je razlika deljiva sa 3,
  5: a ako imaju razlicit ostatak onda je zbir deljiv sa 3. 
  6: U oba slucaja proizvod je deljiv sa 3. Kako je deljiv i sa 3  i sa 4 onda je deliv i sa 12 *)
theorem
  assumes "prost a" "prost b" "a>b" "a>3" "b>3" 
  shows "deljiv_12 ((a+b)*(a-b))"
  sorry


(*1. Prosti brojevi veci od tri su neparni*)
lemma prosti_brojevi_veci_od_tri_neparni:
  assumes "prost x" "x > 3"
  shows "x mod 2 = 1"
  using assms
  unfolding prost_def
  by (metis One_nat_def Suc_leI atLeastAtMost_iff gcd_nat.order_iff_strict linorder_not_less not_numeral_less_one numerals(2) odd_iff_mod_2_eq_one odd_one one_less_numeral_iff semiring_norm(77))

(*2.1.Zbir i razlika dva neparna broja su paran broj*)
lemma razlika_neparnih_paran:
  assumes"prost x" "x > 3" "prost y" "y > 3"
  shows "(x - y) mod 2 = 0"
  using assms 
  by (metis prosti_brojevi_veci_od_tri_neparni One_nat_def  diff_is_0_eq dvd_imp_mod_0 linorder_not_less mod_0 mod_eq_dvd_iff_nat numerals(2) order_le_less )

lemma zbir_nepanih_paran:
  assumes "prost x" "x > 3" "prost y" "y > 3"
  shows "(x + y) mod 2 = 0"
  using assms 
  by (metis add_self_mod_2 mod_add_eq prosti_brojevi_veci_od_tri_neparni)

(*2.2.1. Proizvod parnih brojeva je paran*)
lemma proizvod_parnih_paran:
  assumes  "x mod 2 = 0" "y mod 2 = 0" "prost x" "prost y"
  shows "(x*y) mod 2 = 0"
  using assms
  unfolding prost_def
  by fastforce

(*2.2.2 Proizvod parnih je paran broj deljiv sa cetiri*)

lemma dvocifren_zavrsetak_mod_100: "dvocifren_zavrsetak x = x mod 100"
proof (cases "x < 9")
  case True
  thus ?thesis
    unfolding dvocifren_zavrsetak_def
    by (simp add: izdvoj_cifre.simps)
next
  case False
  thus ?thesis
    using dvocifre_zavrsetak_bez_liste[of x]
    apply simp (*ovo je nama ostavljeno*)
    sorry
qed
          
(*lema koja spaja matematicku definiciju sa definicijom preko cifara - na ovaj nacin treba i za ostale*)
lemma deljiv_4_k: "deljiv_4 x \<longleftrightarrow> (\<exists> k. x = 4 * k)" 
proof
  assume "deljiv_4 x"
  show "\<exists> k. x = 4 * k"
  proof-
    from `deljiv_4 x`
    have "(x mod 100) mod 4 = 0"
      unfolding deljiv_4_def
      using dvocifren_zavrsetak_mod_100[of x]
      by auto
    have "x = 100 * (x div 100) + x mod 100"
      by auto
    hence "x mod 4 = 0"
      using `(x mod 100) mod 4 = 0`
      by (metis Euclidean_Division.div_eq_0_iff add_diff_cancel_left' add_self_mod_2 mod_0_imp_dvd mod_mod_cancel mult_2 mult_mod_right numeral.simps(2) numeral_code(1) numerals(2) odd_one odd_two_times_div_two_nat plus_1_eq_Suc rel_simps(51) zero_less_diff)
    thus ?thesis
      by (simp add: mod_eq_0D)
  qed
next
  assume "\<exists> k. x = 4 * k"
  show "deljiv_4 x"
    sorry
qed


lemma proizvod_parnih_deljiv_sa_cetiri: (*dokazana na konsultacijama*)
  assumes "x mod 2 = 0" "y mod 2 = 0" "prost x" "prost y"
  shows "deljiv_4 (x*y)"
proof-
  from `x mod 2 = 0` obtain k where "x = 2 * k"
    by blast
  moreover
  from `y mod 2 = 0` obtain k' where "y = 2 * k'"
    by blast
  ultimately
  have "x * y = 4 * k * k'"
    by auto
  thus ?thesis
    using deljiv_4_k[of "x*y"]
    by auto
qed

(*3. Ako je broj veci od 3 i prost - onda pri deljenju sa brojem 3 ostatak moze biti 1 ili 2*)
lemma ostatak_pri_deljenju_sa_3: (*PROBLEM*)
  assumes "x > 3" "prost x"
  shows "(x mod 3 = 1) \<or> (x mod 3 = 2)"
  using assms 
  unfolding prost_def
  sorry

(*4. Ako dva broja koja su veca od tri i prosti su daju isti ostatak pri deljenju sa 3
- razlika im je deljiva sa 3*)
lemma razlika_sa_tri:
  assumes "x > 3" "y > 3" "prost x" "prost y"
  assumes "x mod 3 = y mod 3"
  shows "deljiv_3 (x - y) "
  using assms
  unfolding deljiv_3_def prost_def
  by (smt Suc3_eq_add_3 Suc_le_mono add.right_neutral add_le_cancel_left 
      diff_Suc_Suc diff_is_0_eq dvd_9_suma_cifara dvd_eq_mod_eq_0 le0 le_0_eq 
      linorder_not_less mod_0 mod_eq_dvd_iff_nat numerals(2) order_le_less suma_cifara_manja zero_less_diff)

(*5. Ako dva broja daju razlicit ostatak pri deljenju sa 3 i prosti su i veci su od 3
- njihov zbir je deljiv sa tri*)
lemma zbir_sa_tri: (*PROBLEM*)
  assumes "x > 3" "y > 3" "prost x" "prost y"
  assumes "(x mod 3) \<noteq> (y mod 3)"
  shows "deljiv_3 (x + y)"
  using assms
  unfolding deljiv_3_def prost_def
  sorry

(*6. Nezavinso kakav je ostatak (pri deljejnju sa 3) proizvod brojeva x i y za koje vazi da su: prosti i veci od 3
njihov proizvod je deljiv sa tri*)
lemma proizvod_sa_tri: (*PROBLEM*)
  assumes "x > 3" "y > 3" "prost x" "prost y"
  shows "deljiv_3 (x*y)"
  using assms
  unfolding prost_def deljiv_3_def
  sorry

(*Kad dokazemo da je proizvod deljiv sa 3 i proizvod deljiv sa cetiri, upotrebimo te dve leme 
i imamo dokaz da je proizvod deljiv sa 12.

Koristili smo u lemama opsti slucaj za neka dva broja, a u glavnoj teoremi cemo to primeniti na
brojeve (a-b) i (a+b)*)
end