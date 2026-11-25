/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomParameterAdjunction
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Transport of normalized integral Hom counits

Source: Stacks Project, sites-cohomology.tex, Lemma 08J9.
(blueprint: lem-sf-integral-hom-evaluation-transport).

The supplied tensor presentation retains the parameter coherence of tensor-Hom
currying. Uniqueness of left adjoints therefore compares it with the native closed
structure, including its counits, naturally in both tensor arguments.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralHom

noncomputable def swapTensor {D : Type*} [Category D] (T : D × D ⥤ D) :
    D × D ⥤ D := Functor.uncurry.obj (Functor.flip (Functor.curry.obj T))

noncomputable def transportedCounit (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R)
    (S : CoefficientClosedStructure (hom.{u, u} X R))
    (e : a.tensor ≅ swapTensor S.tensor) (K W : Derived.{u, u} X R) :
    ((Functor.curry.obj (hom.{u, u} X R)).obj (op K) ⋙
      (Functor.curry.obj a.tensor).obj K).obj W ⟶ W := by
  with_unfolding_all
    exact e.hom.app (K, (hom.{u, u} X R).obj (op K, W)) ≫
      (S.adjunction K).counit.app W

private def parameterLeftAdjointIso {D : Type*} [Category D]
    {F F' : D ⥤ D ⥤ D} {G : Dᵒᵖ ⥤ D ⥤ D}
    (a : F ⊣₂ G) (b : F' ⊣₂ G) : F ≅ F' :=
  NatIso.ofComponents (fun K ↦ (a.adj K).leftAdjointUniq (b.adj K)) (by
    intro K K' f
    ext L
    dsimp only [NatTrans.comp_app]
    apply ((a.adj K).homEquiv L _).injective
    have h := a.homEquiv_naturality_one f
      (((a.adj K').leftAdjointUniq (b.adj K')).hom.app L)
    dsimp only [ParametrizedAdjunction.homEquiv] at h
    rw [h, Adjunction.homEquiv_leftAdjointUniq_hom_app,
      Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    exact (NatTrans.congr_app (b.unit_whiskerRight_map f) L).symm)

/-- The supplied counits are the transport of a closed native counit.

Source: Stacks Project, sites-cohomology.tex, Lemma 08J9, functorial tensor-Hom
currying. Proof: choose the native closed structure. Its counit compatibility gives
an adjunction with a parameter for the exchanged tensor. For each first argument,
use uniqueness of left adjoints with the common recorded right adjoint. Applying
the source Hom equivalence to the first-variable naturality equation reduces it to
the parameter unit law for the native adjunction. Thus the pointwise comparisons
form a natural isomorphism of curried bifunctors. Lift it through fully faithful
currying. The uniqueness-of-left-adjoints counit identity gives the required
transport equality. No representative choices or boundedness hypotheses are used.
(blueprint: lem-sf-integral-hom-evaluation-transport). -/
theorem tensorPresentation_counit_transport (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R) :
    ∃ S : CoefficientClosedStructure (hom.{u, u} X R),
      ∃ e : a.tensor ≅ swapTensor S.tensor,
        ∀ (K W : Derived.{u, u} X R),
          transportedCounit X R a S e K W = (a.adjunction K).counit.app W := by
  let J := ProEt.topology X
  let : HasSheafify J AddCommGrpCat.{u + 1} := integralCoefficientAbSheafify.{u, u} X
  let : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, u} X
  let : HasDerivedCategory (Modules.{u, u} X R) := HasDerivedCategory.standard _
  obtain ⟨S, _T, _β, _hc⟩ :=
    CategoryTheory.ringedDerived_closed_symmetric_monoidal.{u + 1, u, u, u + 2} J R
  let A : Functor.curry.obj a.tensor ⊣₂ Functor.curry.obj (hom.{u, u} X R) :=
    a.parameterAdjunction
  let b (K : Derived.{u, u} X R) :
      @MonoidalCategory.tensorRight _ _ S.monoidal K ≅
        (Functor.curry.obj (swapTensor S.tensor)).obj K :=
    NatIso.ofComponents (fun L ↦ Iso.refl _) (by
      intro L L' f
      simp [swapTensor, CoefficientClosedStructure.tensor])
  let B : Functor.curry.obj (swapTensor S.tensor) ⊣₂
      Functor.curry.obj (hom.{u, u} X R) :=
    parameterAdjunctionOfCounit (fun K ↦ (S.adjunction K).ofNatIsoLeft (b K)) (by
      intro K K' W f
      simpa [b, swapTensor, CoefficientClosedStructure.tensor] using
        S.evaluation_naturality K' K W f)
  have hb (K W : Derived.{u, u} X R) :
      (B.adj K).counit.app W = (S.adjunction K).counit.app W := by
    change (𝟙 _) ≫ (S.adjunction K).counit.app W = _
    exact Category.id_comp _
  let e : a.tensor ≅ swapTensor S.tensor :=
    Functor.fullyFaithfulCurry.preimageIso (parameterLeftAdjointIso A B)
  refine ⟨S, e, ?_⟩
  intro K W
  have he : Functor.curry.map e.hom = (parameterLeftAdjointIso A B).hom :=
    Functor.fullyFaithfulCurry.map_preimage _
  have he' := congrArg (fun n ↦ (n.app K).app
    ((hom.{u, u} X R).obj (op K, W))) he
  change e.hom.app (K, (hom.{u, u} X R).obj (op K, W)) =
    ((A.adj K).leftAdjointUniq (B.adj K)).hom.app
      ((hom.{u, u} X R).obj (op K, W)) at he'
  with_unfolding_all
    change e.hom.app (K, (hom.{u, u} X R).obj (op K, W)) ≫
        (S.adjunction K).counit.app W = (a.adjunction K).counit.app W
    rw [he', ← hb K W]
    exact Adjunction.leftAdjointUniq_hom_app_counit (a.adjunction K) (B.adj K) W

/-- The transported native counits are natural in the first tensor variable.

Source: Stacks Project, sites-cohomology.tex, Lemma 08J9.  Proof: expand
`transportedCounit`; naturality of `e` changes the supplied tensor map into the
swapped native tensor map, and `CoefficientClosedStructure.evaluation_naturality`
then gives the equality.  This is a purely formal categorical calculation.
(blueprint: lem-sf-integral-hom-evaluation-transport-naturality). -/
theorem transportedCounit_naturality (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R)
    (S : CoefficientClosedStructure (hom.{u, u} X R))
    (e : a.tensor ≅ swapTensor S.tensor)
    (K K' W : Derived.{u, u} X R) (f : K' ⟶ K) :
    a.tensor.map (Prod.mkHom (𝟙 K')
      ((hom.{u, u} X R).map (Prod.mkHom f.op (𝟙 W)))) ≫
        transportedCounit X R a S e K' W =
      a.tensor.map (Prod.mkHom f (𝟙 _)) ≫
        transportedCounit X R a S e K W := by
  with_unfolding_all
    simp only [transportedCounit]
    erw [e.hom.naturality_assoc, e.hom.naturality_assoc]
    congr 1
    simpa [swapTensor, CoefficientClosedStructure.tensor] using
      S.evaluation_naturality K K' W f

end WeilConjectures.IntegralHom
