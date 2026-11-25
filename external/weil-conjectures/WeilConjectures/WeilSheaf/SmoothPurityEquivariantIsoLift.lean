/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityEquivariantLift
public import WeilConjectures.WeilSheaf.SmoothPurityCanonicalFinite

/-! # Equivariant isomorphisms reconstructed in the bounded constructible category -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {X : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- Reduction modulo the coefficient prime detects invertibility of a morphism between
bounded constructible integral complexes, even when the morphism is given in the ambient
category. -/
theorem isIso_of_purityIntegralReduction_map
    {K L : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧}
    (f : K.obj ⟶ L.obj)
    (hf : IsIso ((purityIntegralReduction X.left ℓ E.1 1).map f)) : IsIso f := by
  let ι := (boundedConstructible
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)).ι
  let g : K ⟶ L := (ObjectProperty.fullyFaithfulι _).preimage f
  have hg : ι.map g = f := (ObjectProperty.fullyFaithfulι _).map_preimage f
  have hmap : IsIso
      ((Mod.extendScalars (integersModPowReduction X.left ℓ E.1 1)).leftDerivedFunctor.map
        (ι.map g)) := by
    rw [hg]
    exact hf
  have hredι := (NatIso.isIso_map_iff
    (boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E.1 1) g).2 hmap
  change IsIso ((boundedConstructible
    (condensedRingObj (Profinite.integersModPowRingObj ℓ E.1 1) X.left)).ι.map
    ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 1).map g)) at hredι
  have hred : IsIso ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 1).map g) :=
    isIso_of_reflects_iso _ (boundedConstructible _).ι
  have : IsIso g := isIso_of_isIso_etaleReduction_map ℓ E.1 one_ne_zero g (by
    change IsIso ((finiteEtaleReading ℓ E.1 1 X).map
      ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 1).map g))
    infer_instance)
  rw [← hg]
  infer_instance

set_option hygiene false in
local notation "𝐃₀" => DerivedCategory (Mod (Sheaf (ProEt.topology X.left) Ab.{u + 1})
  (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left))
set_option hygiene false in
local notation "𝐃ₙ(" n ")" => DerivedCategory (Mod (Sheaf (ProEt.topology X.left) Ab.{u + 1})
  (condensedRingObj (Profinite.integersModPowRingObj ℓ E.1 (n + 1)) X.left))

/-- Finite equivariant isomorphisms stable under ordinary reduction give an integral
isomorphism with the specified Weil data. No canonical choice of finite orientations is
required. -/
theorem exists_equivariant_iso_of_finite_reductions
    (G : 𝐃₀ ⥤ 𝐃₀) (Gn : ∀ n : ℕ, 𝐃ₙ(n) ⥤ 𝐃ₙ(n))
    (c : ∀ n : ℕ, G ⋙ purityIntegralReduction X.left ℓ E.1 (n + 1) ≅
      purityIntegralReduction X.left ℓ E.1 (n + 1) ⋙ Gn n)
    (K L : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (φK : G.obj K.obj ⟶ K.obj) (φL : G.obj L.obj ⟶ L.obj)
    [∀ n : ℕ, Finite ((G.obj K.obj) ⟦(1 : ℤ)⟧ ⟶
      (Mod.comap (integersModPowReduction X.left ℓ E.1 (n + 1))).mapDerivedCategory.obj
        ((purityIntegralReduction X.left ℓ E.1 (n + 1)).obj L.obj))]
    (hfin : ∀ n : ℕ, Finite
      ((purityIntegralReduction X.left ℓ E.1 (n + 1)).obj K.obj ⟶
        (purityIntegralReduction X.left ℓ E.1 (n + 1)).obj L.obj))
    (hne : ∀ n : ℕ, ∃ e :
      (purityIntegralReduction X.left ℓ E.1 (n + 1)).obj K.obj ≅
        (purityIntegralReduction X.left ℓ E.1 (n + 1)).obj L.obj,
      PurityReductionWeilCondition G Gn c φK φL n e.hom)
    (hstep : ∀ n s, PurityReductionWeilCondition G Gn c φK φL (n + 1) s →
      PurityReductionWeilCondition G Gn c φK φL n (derivedReductionStep (n + 1) s)) :
    ∃ e : K ≅ L, IsWeilEquivariant G φK φL e.hom.hom := by
  have hL : derivedCompleteIntegers ℓ E.1 X.left L.obj := by
    have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
    exact derivedCompleteIntegers_of_boundedConstructible L.property
  have h := exists_equivariant_forall_isIso_derivedReduction_map G Gn c φK φL
    hL hfin hne hstep
  obtain ⟨f, hf, hfiso⟩ := h
  have := isIso_of_purityIntegralReduction_map ℓ E (K := K) (L := L) f (hfiso 0)
  let e := (ObjectProperty.fullyFaithfulι (boundedConstructible
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left))).preimageIso (asIso f)
  refine ⟨e, ?_⟩
  have he : e.hom.hom = f :=
    (ObjectProperty.fullyFaithfulι _).map_preimage f
  rw [he]
  exact hf

end AlgebraicGeometry.ProEtale.CondensedRing
