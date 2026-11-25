/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData

/-! # Transport between normalized pro-etale tensor models -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOrdinary
attribute [local implicit_reducible] Functor.map₂HomologicalComplex
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  proEtaleRingDerivedPullbackFactors proEtaleTensorPullbackTotalIso
  Functor.mapDerivedCategory

/-- Two signed K-flat tensor presentations have a normalized comparison isomorphism.
Source: Stacks 07A4, 0G7E and 04VK.
(blueprint: lem-sf-integral-tensor-model-identification).

Proof: restrict natural transformations along the product of the resolving-class
localizations. This restriction is fully faithful. Lift the inverse of the first
representative isomorphism followed by the second. The map-preimage equation,
evaluated on a representative pair, gives the asserted normalization. -/
theorem tensorModelIso (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (a b : ProEtaleTensorModel W R) :
    ∃ e : a.tensor ≅ b.tensor,
      ∀ (P Q : CochainComplex (proEtaleRingModules W R) ℤ)
        (hP : proEtaleFlatRepresentatives W R P)
        (hQ : proEtaleFlatRepresentatives W R Q),
        a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
          e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        b.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) := by
  obtain ⟨ff⟩ := tensorRepresentatives_fullyFaithful R R
  let e := ff.preimageIso (a.representative.symm ≪≫ b.representative)
  refine ⟨e, ?_⟩
  intro P Q hP hQ
  have he := congrArg (fun t ↦ t.app (⟨P, hP⟩, ⟨Q, hQ⟩))
    (ff.map_preimage (a.representative.symm ≪≫ b.representative).hom)
  change e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) = _ at he
  rw [he]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.hom_inv_id_app_assoc]

/-- Canonical tensor pullback commutes with normalized changes of tensor model.
Source: Stacks 07A4, 0G7E and 04VK.
(blueprint: lem-sf-integral-tensor-model-pullback-transport).

Proof: full faithfulness of product resolving-class restriction reduces the equality
of natural transformations to flat-term K-flat pairs. Precompose with the source
representative isomorphism and postcompose with the tensor of the pullback computation
isomorphisms. Apply the two defining canonical pullback equations. The normalization
at the source, naturality of the target model isomorphism, and its normalization on
the pulled representatives identify the resulting composites. Cancel isomorphisms. -/
theorem tensorModelPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (aY bY : ProEtaleTensorModel Y R)
    (aX bX : ProEtaleTensorModel X S)
    (eY : aY.tensor ≅ bY.tensor) (eX : aX.tensor ≅ bX.tensor)
    (heY : ∀ (P Q : CochainComplex (proEtaleRingModules Y R) ℤ)
      (hP : proEtaleFlatRepresentatives Y R P)
      (hQ : proEtaleFlatRepresentatives Y R Q),
      aY.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
        eY.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      bY.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩))
    (heX : ∀ (P Q : CochainComplex (proEtaleRingModules X S) ℤ)
      (hP : proEtaleFlatRepresentatives X S P)
      (hQ : proEtaleFlatRepresentatives X S Q),
      aX.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
        eX.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      bX.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩))
    (M N : DerivedCategory (proEtaleRingModules Y R)) :
    let F := proEtaleRingDerivedPullback f R S c
    let α := proEtaleCanonicalTensorComparison f
      R S
      c aY aX
    let β := proEtaleCanonicalTensorComparison f
      R S
      c bY bX
    F.map (eY.hom.app (M, N)) ≫ β.hom.app (M, N) =
      α.hom.app (M, N) ≫ eX.hom.app (F.obj M, F.obj N) := by
  dsimp only
  let F := proEtaleRingDerivedPullback f R S c
  let α := proEtaleCanonicalTensorComparison f
    R S
    c aY aX
  let β := proEtaleCanonicalTensorComparison f
    R S
    c bY bX
  let left := Functor.whiskerRight eY.hom F ≫ β.hom
  let right := α.hom ≫ Functor.whiskerLeft (F.prod F) eX.hom
  suffices hh : left = right from congrArg (fun z ↦ z.app (M, N)) hh
  obtain ⟨_, ⟨ff⟩, _⟩ := proEtaleTensorPullbackDescentData f
    R S
    c
  apply ff.map_injective
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨⟨P, hp⟩, ⟨Q, hq⟩⟩
  obtain ⟨hp', hq', ha⟩ := (proEtaleCanonicalTensorPullback f
    R S
    c aY aX).2.exists.choose_spec P Q hp hq
  obtain ⟨_, _, hb⟩ := (proEtaleCanonicalTensorPullback f
    R S
    c bY bX).2.exists.choose_spec P Q hp hq
  let ε := proEtaleRingDerivedPullbackFactors f
    R S
    c
  change F.map (aY.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
    α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫ _ = _ at ha
  change F.map (bY.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
    β.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫ _ = _ at hb
  change F.map (eY.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      β.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
    α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      eX.hom.app (F.obj (DerivedCategory.Q.obj P), F.obj (DerivedCategory.Q.obj Q))
  apply (cancel_epi (F.map (aY.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)))).1
  apply (cancel_mono (bX.tensor.mapIso (Iso.prod (ε.app P) (ε.app Q))).hom).1
  have hn := eX.hom.naturality (Prod.mkHom (ε.hom.app P) (ε.hom.app Q))
  simp only [Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom, Category.assoc]
  rw [← F.map_comp_assoc, heY, hb]
  have hn' := congrArg (fun z ↦
    F.map (aY.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫ z) hn
  have ha' := congrArg (fun z ↦ z ≫ eX.hom.app
    (DerivedCategory.Q.obj
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P),
     DerivedCategory.Q.obj
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj Q))) ha
  have he' := congrArg (fun z ↦
    ε.hom.app (P.mapBifunctor Q (proEtaleOrdinaryTensor Y R)) ≫
      (DerivedCategory.Q.mapIso (proEtaleTensorPullbackTotalIso f R S c P Q)).inv ≫ z)
    (heX _ _ hp' hq')
  simp only [Category.assoc] at ha'
  exact (ha'.trans he').symm.trans hn'

end WeilConjectures.IntegralOrdinary
