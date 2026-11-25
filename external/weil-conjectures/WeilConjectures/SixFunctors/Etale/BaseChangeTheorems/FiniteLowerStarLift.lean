/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.EdgeMapBaseChange
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Lifting `H¹`-classes of finite pushforwards from the closed fibre

Let `(A, I)` be a henselian pair, `X` a scheme over `A` with closed fibre `ι : X₀ ⟶ X`, and
`h : V ⟶ X` a finite morphism with `V` proper over `A`. For a finite abelian group `M`, every
class of `H¹(X₀, ι^* h_* M)` comes from `H¹(X, h_* M)`. This is the lifting step in the proof
of the acyclicity of restricted injectives on `ℙ¹` over a strictly henselian ring (blueprint
`lemma-acyclicity-closed-fibre--1`).

## Main statements

- `AlgebraicGeometry.Etale.surjective_cohomologyMap_one_lowerStar_constantSheaf`: the lifting.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.Etale

open Scheme

/-- **Classes of finite pushforwards of finite constant sheaves lift from the closed fibre.**
Let `(A, I)` be a henselian pair, `p : X ⟶ Spec A` with closed fibre `ι : X₀ ⟶ X`, and
`h : V ⟶ X` finite with `V` proper over `A`. For a finite abelian group `M`, restriction
`H¹(X, h_* M) ⟶ H¹(X₀, ι^* h_* M)` is surjective: by the finite exchange `ι^* h_* = h₀_* ι_V^*` and
the bijectivity of the Leray edge maps along the finite `h` and `h₀`, it is identified, up to
an automorphism, with restriction `H¹(V, M) ⟶ H¹(V₀, M)`, which is bijective by the `H¹`
comparison over a henselian pair. -/
theorem surjective_cohomologyMap_one_lowerStar_constantSheaf {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I] {X X₀ V V₀ : Scheme.{u}} (p : X ⟶ Spec (.of A))
    (ι : X₀ ⟶ X) (p₀ : X₀ ⟶ Spec (.of (A ⧸ I)))
    (hX : IsPullback ι p₀ p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (h : V ⟶ X) [IsFinite h] [IsProper (h ≫ p)] (ιV : V₀ ⟶ V) (h₀ : V₀ ⟶ X₀)
    (hV : IsPullback ιV h₀ h ι) (M : Type (u + 1)) [AddCommGroup M] [Finite M] :
    Function.Surjective (cohomologyMap ι (((h)_*[AddCommGrpCat.{u + 1}]).obj
      ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M))) 1) := by
  have : IsFinite h₀ := MorphismProperty.of_isPullback hV inferInstance
  set F := (constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)
  have hβ : IsIso ((baseChangeMap AddCommGrpCat.{u + 1} hV.toCommSq).app F) := by
    have := isIso_baseChangeMap_of_isFinite AddCommGrpCat.{u + 1} hV
    infer_instance
  obtain ⟨α, hα⟩ := exists_edgeMap_baseChangeMap_cohomologyMap hV.toCommSq F 1
  have hT := bijective_cohomologyMap_one_constantSheaf_of_henselianRing I (h ≫ p) ιV (h₀ ≫ p₀)
    (hV.paste_vert hX) M
  have hE := bijective_edgeMap_of_isFinite h F 1
  have hE₀ := bijective_edgeMap_of_isFinite h₀ (((ιV)^*[AddCommGrpCat.{u + 1}]).obj F) 1
  have hβ' : Function.Bijective (Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1}
      hV.toCommSq).app F) 1) := by
    refine ⟨injective_sheafHMap_of_isIso _ 1, fun y ↦ ⟨Sheaf.H.map (inv ((baseChangeMap
      AddCommGrpCat.{u + 1} hV.toCommSq).app F)) 1 y, ?_⟩⟩
    rw [← Sheaf.H.map_comp_apply, IsIso.inv_hom_id, Sheaf.H.map_id_apply]
  intro x
  obtain ⟨z, hz⟩ := hT.2 ((Ext.mk₀ α.inv).comp
    (Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h₀).counit.app
      (((ιV)^*[AddCommGrpCat.{u + 1}]).obj F)) 1 (cohomologyMap h₀ _ 1
        (Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} hV.toCommSq).app F) 1 x)))
    (zero_add 1))
  obtain ⟨y, hy⟩ := hE.2 z
  refine ⟨y, (hE₀.1.comp hβ'.1) ?_⟩
  dsimp only [Function.comp_apply] at hy ⊢
  rw [hα y, hy, show cohomologyMap ιV ((𝟭 _).obj F) 1 z = _ from hz,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
    Ext.mk₀_id_comp]
end AlgebraicGeometry.Etale
