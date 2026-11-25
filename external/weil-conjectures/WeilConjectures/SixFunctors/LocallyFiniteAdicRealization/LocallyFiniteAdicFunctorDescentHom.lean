/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicNormalizedFunctorData
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedStageComparison
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SplitCoefficientDerivedFaithfulSupplement

/-! # Hom descent for a normalized locally finite adic functor

Source: Bhatt--Scholze, Proposition 6.8.14(1),(2), using the existing condensed
filtered two-colimit; native realization proof steps 3 and 6.
(blueprint: lem-sf-locally-finite-adic-functor-descent-hom)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

attribute [local irreducible] sections CoefficientPresentation.integralMap
  completedTensorComparison

private theorem finiteCondensed_faithful (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :
    (ProEtale.constructibleToPadicAlgCl X l E).Faithful := by
  letI := ProEtale.faithful_leftDerivedExtendScalarsToPadicAlgCl X l E
  let I := (ProEtale.boundedConstructible (ProEtale.padicAlgClRingObj X l)).ι
  haveI : (ProEtale.constructibleToPadicAlgCl X l E ⋙ I).Faithful :=
    inferInstanceAs (((ProEtale.boundedConstructible
      (ProEtale.padicSubfieldRingObj X l E)).ι ⋙
        ProEtale.derivedExtendScalarsToPadicAlgCl X l E).Faithful)
  exact Functor.Faithful.of_comp (ProEtale.constructibleToPadicAlgCl X l E) I

attribute [local irreducible] nativeCondensedDerived nativeCondensedModules

/-- The normalized native functor is fully faithful on derived Hom sets.

Source: Bhatt--Scholze, Proposition 6.8.14(1),(2).
Proof in words: use the finite coefficient comparisons, which identify a representative
with its condensed tensor realization. For injectivity represent both arrows at one
common field. Cancel the object comparisons and tensor associators. The split inclusion
of the finite coefficient field into the closure makes derived extension faithful;
finite realization is also faithful, so the representatives agree. For surjectivity
transport the ambient arrow to condensed modules. Hom-surjectivity of the existing
condensed two-colimit puts it at a common finite field. Conjugate by the scalar
comparisons and lift it through the full finite realization. The representative formula
identifies its native image with the original arrow. This applies to every source pair,
including shifted objects, without asserting an essential-image or smallness result.
(blueprint: lem-sf-locally-finite-adic-functor-descent-hom)
-/
theorem normalizedFunctor_descent_hom
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] (D : NormalizedFunctor l X) :
    ∀ K L, Function.Bijective (D.J.map : (K ⟶ L) → (D.J.obj K ⟶ D.J.obj L)) := by
  obtain ⟨C⟩ := condensedStageComparison_exists l X D
  intro K L
  constructor
  · intro f g h
    obtain ⟨M, _, hK, hL, hK', hL', u, v, rfl, rfl⟩ :=
      StageSystem.PairCategory.exists_common_stage f g K.stage
    have he := congrArg (fun t ↦ (nativeCondensedDerived l X).map t) h
    have he := (C.representative M hK hL u).symm.trans
      (he.trans (C.representative M hK hL v))
    have he := (cancel_epi (C.objectIso K).hom).mp he
    have he := (cancel_mono (C.objectIso L).inv).mp he
    have he := ObjectProperty.hom_ext _ he
    have he := (cancel_epi
      ((ProEtale.constructibleToPadicAlgClCompIso X l hK).inv.app
        ((C.finite K.stage).obj K.obj))).mp he
    have he := (cancel_mono
      ((ProEtale.constructibleToPadicAlgClCompIso X l hL).hom.app
        ((C.finite L.stage).obj L.obj))).mp he
    letI := finiteCondensed_faithful l X M
    have he := (ProEtale.constructibleToPadicAlgCl X l M).map_injective he
    have he := (cancel_epi ((C.scalar hK).hom.app K.obj)).mp he
    have he := (cancel_mono ((C.scalar hL).inv.app L.obj)).mp he
    letI := C.faithful M
    have he := (C.finite M).map_injective he
    exact congrArg (StageSystem.PairCategory.mkHom M hK hL) he
  · intro f
    let f' :
        (ProEtale.constructibleToPadicAlgCl X l K.stage).obj
            ((C.finite K.stage).obj K.obj) ⟶
          (ProEtale.constructibleToPadicAlgCl X l L.stage).obj
            ((C.finite L.stage).obj L.obj) :=
      ObjectProperty.homMk ((C.objectIso K).inv ≫
        (nativeCondensedDerived l X).map f ≫ (C.objectIso L).hom)
    obtain ⟨M, hK, hL, g, hg⟩ :=
      (ProEtale.constructibleCocone_isFilteredTwoColimit X l).homSurj
        K.stage L.stage ((C.finite K.stage).obj K.obj)
        ((C.finite L.stage).obj L.obj) f'
    dsimp only [ProEtale.constructibleCocone] at g hg
    let t := (C.scalar hK).inv.app K.obj ≫ g ≫ (C.scalar hL).hom.app L.obj
    letI := C.full M
    let u := (C.finite M).preimage t
    refine ⟨StageSystem.PairCategory.mkHom M hK hL u, ?_⟩
    apply (nativeCondensedDerived l X).map_injective
    rw [C.representative M hK hL u]
    have hu : (C.scalar hK).hom.app K.obj ≫ (C.finite M).map u ≫
        (C.scalar hL).inv.app L.obj = g := by
      simp only [u, t, Functor.map_preimage, Category.assoc,
        Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Category.comp_id]
      erw [Category.comp_id]
    have hh :
        (ProEtale.constructibleToPadicAlgClCompIso X l hK).inv.app
              ((C.finite K.stage).obj K.obj) ≫
            (ProEtale.constructibleToPadicAlgCl X l M).map
              ((C.scalar hK).hom.app K.obj ≫ (C.finite M).map u ≫
                (C.scalar hL).inv.app L.obj) ≫
            (ProEtale.constructibleToPadicAlgClCompIso X l hL).hom.app
              ((C.finite L.stage).obj L.obj) = f' := by
      rw [hu]
      exact hg.symm
    have hh := congrArg (fun a ↦ (C.objectIso K).hom ≫ a.hom ≫ (C.objectIso L).inv) hh
    refine hh.trans ?_
    change (C.objectIso K).hom ≫
      ((C.objectIso K).inv ≫ (nativeCondensedDerived l X).map f ≫
        (C.objectIso L).hom) ≫ (C.objectIso L).inv = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

end WeilConjectures.LocallyFiniteAdicRealization
