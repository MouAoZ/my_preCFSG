import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Data.Set.Finite.Basic
import Mathlib.GroupTheory.Subgroup.Simple
set_option linter.all false

-- We work with a finite group G
variable {G : Type*} [Group G] [Finite G]

-- 1. Definition of a Minimal Normal Subgroup
def IsMinimalNormal (N : Subgroup G) : Prop :=
  N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N

-- 2. Formalizing the collection X of nonabelian simple normal subgroups
-- We use sSup X = ⊤ to represent that the product of the members of X is the whole group G.
structure SemisimpleCollection (X : Set (Subgroup G)) : Prop where
  normal : ∀ S ∈ X, S.Normal
  simple : ∀ S ∈ X, IsSimpleGroup S
  nonabelian : ∀ S ∈ X, ¬ (∀ a b : S, Commute a b)
  product_eq_top : sSup X = ⊤



-- 3. Definition of an Internal Direct Product for a set of subgroups
-- A set of normal subgroups forms an internal direct product if each subgroup
-- intersects trivially with the product (supremum) of all the others.
def IsInternalDirectProduct (X : Set (Subgroup G)) : Prop :=
  ∀ T ∈ X, T ⊓ sSup (X \ {T}) = ⊥


omit [Finite G]
theorem nontrivial_group (X : Set (Subgroup G)) (hX : SemisimpleCollection X) (S : Subgroup G) (hS : S ∈ X): S ≠ ⊥ := by
  by_contra h_eq_bot
  have h_abelian : ∀ a b : S, Commute a b := by
    intro a b
    have ha : a.1 = 1 := Subgroup.mem_bot.mp (by rw [←h_eq_bot]; exact a.2)
    have hb : b.1 = 1 := Subgroup.mem_bot.mp (by rw [←h_eq_bot]; exact b.2)
    have ha_S : a = 1 := Subtype.ext ha
    have hb_S : b = 1 := Subtype.ext hb
    rw [ha_S, hb_S]
  exact hX.nonabelian S hS h_abelian



-- 4. The Main Theorem and Proof Structure
theorem semisimple_structure (X : Set (Subgroup G)) (hX : SemisimpleCollection X) :
    IsInternalDirectProduct X ∧ X = {N : Subgroup G | IsMinimalNormal N} := by

  -- "The members of X are clearly minimal normal subgroups of G"
  have h_X_min_normal : ∀ S ∈ X, IsMinimalNormal S := by
    intro S hS
    refine ⟨hX.normal S hS, ?_, ?_⟩
    exact nontrivial_group X hX S hS
    intro M hM hMS
    have h_S_simple : IsSimpleGroup S := hX.simple S hS
    let M' : Subgroup S := M.subgroupOf S
    have hM' : M'.Normal := hM.subgroupOf S
    have h_bot_top := h_S_simple.eq_bot_or_eq_top_of_normal M'
    rcases h_bot_top hM' with h_bot | h_top
    left
    ext x
    simp only [Subgroup.mem_bot]
    constructor
    · intro hx
      -- x is in M, so x is in S (since M ≤ S)
      have hxS : x ∈ S := hMS hx
      -- View x as an element of S to use our M' hypothesis
      have hxM' : (⟨x, hxS⟩ : S) ∈ M' := hx
      -- Since M' = ⊥, this element must be 1
      rw [h_bot, Subgroup.mem_bot] at hxM'
      -- Extract the underlying value to show x = 1
      exact congr_arg Subtype.val hxM'
    · intro hx
      rw [hx]
      exact Subgroup.one_mem M
    right
    ext x
    constructor
    · -- Forward direction: x ∈ M → x ∈ S
      exact fun hx => hMS hx
    · -- Backward direction: x ∈ S → x ∈ M
      intro hxS
      -- View x as an element of S. Since M' = ⊤, it is in M'
      have hxM' : (⟨x, hxS⟩ : S) ∈ M' := by
        rw [h_top]
        exact Subgroup.mem_top _
      -- By definition of subgroupOf, being in M' means being in M
      exact hxM'
  -- "if S ∈ X and N is a minimal normal subgroup of G different from S, then N ∩ S = 1"
  have h_intersect_bot : ∀ S ∈ X, ∀ N, IsMinimalNormal N → N ≠ S → S ⊓ N = ⊥ := by
    intro S hS N hN hNS
    have h_int_normal_S : (S ⊓ N).Normal := by
      have h_S_normal : S.Normal := (h_X_min_normal S hS).1
      have h_N_normal : N.Normal := hN.1
      exact Subgroup.normal_inf_normal S N

    have h_int_le_S : S ⊓ N ≤ S := inf_le_left
    have h_int_le_N : S ⊓ N ≤ N := inf_le_right
    have h_int_S_N_ne_S: S ⊓ N ≠ S := by
      by_contra u
      rw [u] at h_int_le_N
      rw [u] at h_int_normal_S
      have h_S_is_N : S = ⊥ ∨ S = N := hN.2.2 S h_int_normal_S h_int_le_N
      have h_S_not_bot : S ≠ ⊥ := nontrivial_group X hX S hS
      have h_eq : S = N := (or_iff_not_imp_left.mp h_S_is_N) h_S_not_bot
      exact Ne.elim hNS (Eq.symm h_eq)
    exact or_iff_not_imp_right.mp ((h_X_min_normal S hS).2.2 (S ⊓ N) h_int_normal_S h_int_le_S) h_int_S_N_ne_S

  -- "and hence S centralizes N."
  have h_centralize : ∀ S ∈ X, ∀ N, IsMinimalNormal N → N ≠ S →
      ∀ s ∈ S, ∀ n ∈ N, s * n = n * s := by
    intro S hS N hN hNS s hsS n hnN
    have SN1: S ⊓ N = ⊥ := h_intersect_bot S hS N hN hNS
    rw [<- (inv_inv (s*n)), mul_inv_rev]
    symm
    rw [<-mul_eq_one_iff_eq_inv, <-mul_assoc]
    have hSn : S.Normal := (h_X_min_normal S hS).1
    have hNn : N.Normal := hN.1
    have nsninv: n * s * n⁻¹ ∈ S := Subgroup.Normal.conj_mem hSn s hsS n
    have sinv: s⁻¹ ∈ S := (Subgroup.inv_mem_iff S).mpr hsS
    have nsninvsinv_s: n * s * n⁻¹ * s⁻¹ ∈ S := (Subgroup.mul_mem_cancel_right S sinv).mpr nsninv
    have nsninvsinv_n: n * s * n⁻¹ * s⁻¹ ∈ N := by
      rw [mul_assoc, mul_assoc, <-mul_assoc s n⁻¹]
      have ninv_n: n⁻¹ ∈ N := (Subgroup.inv_mem_iff N).mpr hnN
      have sninvsinv_n: s * n⁻¹ * s⁻¹ ∈ N := Subgroup.Normal.conj_mem hNn n⁻¹ ninv_n s
      exact (Subgroup.mul_mem_cancel_right N sninvsinv_n).mpr hnN
    have nsninvsinv_scapn: n * s * n⁻¹ * s⁻¹ ∈ S ⊓ N := by
      rw [Subgroup.mem_inf]
      exact ⟨nsninvsinv_s, nsninvsinv_n⟩
    rw [SN1] at nsninvsinv_scapn
    exact ofMul_eq_zero.mp nsninvsinv_scapn

  constructor
  rw [IsInternalDirectProduct]
  intro T hT
  have h_sSup_normal : (sSup (X \ {T})).Normal := by
    -- We define normality by showing conjugation stays inside the subgroup
    refine Subgroup.Normal.mk (fun g h h_mem => ?_)
    -- Step 1: Expose the closure hiding inside sSup so induction works
    -- rw [Subgroup.sSup_eq_closure] at h_mem ⊢

    -- -- Step 2: Now closure_induction matches the syntax!
    -- induction h_mem using Subgroup.closure_induction with
    -- | mem x hx =>
    --     -- x is an element of one of the subgroups S
    --     simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx
    --     rcases hx with ⟨S, hS_in_X, hxS⟩
    --     have h_norm := hX.normal S hS_in_X.1
    --     have h_conj : g * x * g⁻¹ ∈ S := h_norm.conj_mem x hxS g
    --     -- Push the conjugate back into the closure
    --     apply Subgroup.subset_closure
    --     simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    --     exact ⟨S, hS_in_X, h_conj⟩
    -- | one =>
    --     rw [mul_one, mul_inv_cancel]
    --     exact Subgroup.one_mem _
    -- | mul u v _ _ hu hv =>
    --     -- The 'group' tactic handles the algebra: g(uv)g⁻¹ = (gug⁻¹)(gvg⁻¹)
    --     have h_eq : g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
    --     rw [h_eq]
    --     exact Subgroup.mul_mem _ hu hv
    -- | inv u _ hu =>
    --     -- The 'group' tactic handles: g(u⁻¹)g⁻¹ = (gug⁻¹)⁻¹
    --     have h_eq : g * u⁻¹ * g⁻¹ = (g * u * g⁻¹)⁻¹ := by group
    --     rw [h_eq]
    --     exact Subgroup.inv_mem _ hu
  --   intro S hS
  --   -- hS is the proof that S ∈ X \ {T}
  --   -- hS.1 is the proof that S ∈ X
  --   exact hX.normal S hS.1
  -- have h_int_normal : (T ⊓ sSup (X \ {T})).Normal := by
  --   #check (h_X_min_normal T hT).1
  --   apply (Subgroup.normal_inf_normal T)


-- -- Use h_X_min_normal to branch: intersection is ⊥ or T
-- rcases (h_X_min_normal T hT).2.2 (T ⊓ sSup (X \ {T})) h_int_normal inf_le_left with h_bot | h_top
-- · exact h_bot
-- · -- Derive the contradiction for h_top
--   -- Show that T centralizes sSup (X \ {T}) and thus centralizes itself
--   -- Use hX.nonabelian to close the goal



  -- -- "Let T ∈ X, and let K be the product of all other members of X"
  -- -- In our formalization, K is represented by `sSup (X \ {T})`.

  -- -- "By the result of the first paragraph, K centralizes T."
  -- have h_K_centralizes_T : ∀ T ∈ X, ∀ k ∈ sSup (X \ {T}), ∀ t ∈ T, k.1 * t.1 = t.1 * k.1 := by
  --   sorry

  -- -- "Since T is nonabelian and simple, it has trivial center"
  -- have h_trivial_center : ∀ T ∈ X, Subgroup.center T = ⊥ := by
  --   sorry

  -- -- "T ∩ K ⊆ Z(T) = 1"
  -- -- Because T and K centralize each other, their intersection is in the center of T.
  -- have h_direct : ∀ T ∈ X, T ⊓ sSup (X \ {T}) = ⊥ := by
  --   sorry

  -- -- "It follows that this product is direct"
  -- have h_is_direct_product : IsInternalDirectProduct X := by
  --   exact h_direct

  -- -- "Finally, if N is minimal normal in G and N ∉ X, then N is centralized by Π X = G"
  -- -- Since sSup X = ⊤, centralizing the generators means centralizing all of G.
  -- have h_N_centralized : ∀ N, IsMinimalNormal N → N ∉ X →
  --     ∀ g : G, ∀ n ∈ N, g * n.1 = n.1 * g := by
  --   sorry

  -- -- "and thus N ⊆ Z(G)"
  -- have h_N_in_center : ∀ N, IsMinimalNormal N → N ∉ X → N ≤ Subgroup.center G := by
  --   sorry

  -- -- "But G is a direct product of groups having trivial centers, so Z(G) = 1"
  -- have h_center_G_bot : Subgroup.center G = ⊥ := by
  --   sorry

  -- -- "this contradiction shows that X contains all minimal normal subgroups of G."
  -- have h_X_eq_min_normal : X = {N : Subgroup G | IsMinimalNormal N} := by
  --   sorry

  -- -- Bring the two main conclusions together
  -- exact ⟨h_is_direct_product, h_X_eq_min_normal⟩
