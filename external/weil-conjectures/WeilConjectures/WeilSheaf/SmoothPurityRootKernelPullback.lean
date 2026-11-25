/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.TateTwist.FiniteRootsOfUnity
public import WeilConjectures.TateTwist.RootsOfUnityUpperStar
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement

/-! # Pullback agrees for the two models of pro-étale roots of unity -/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local implicit_reducible] MorphismProperty Scheme.ProEt

/-- The two section identifications of the kernel of the power map agree, because
both identify a section with its image in the sheaf of units. -/
lemma purity_proEtaleRootsOfUnitySections_eq (X : Scheme.{u}) (N : ℕ) (V : X.ProEtᵒᵖ) :
    proEtaleRootsOfUnitySections X N V =
      Scheme.ProEt.rootsOfUnitySheafSectionsEquiv X N V.unop := by
  apply (existsUnique_proEtaleRootsOfUnitySections X N V).unique
  · exact (existsUnique_proEtaleRootsOfUnitySections X N V).exists.choose_spec
  · intro x
    apply ULift.ext
    apply Additive.toMul.injective
    exact Scheme.ProEt.rootsOfUnitySheafSectionsEquiv_apply X N V.unop x

/-- The presheaf of roots is already a sheaf, identified with the kernel of the
power map without making a new choice of root coordinates. -/
noncomputable def purityRootsPresheafKernelIso (X : Scheme.{u}) (N : ℕ) :
    rootsOfUnityPresheafSheaf X N ≅ proEtaleRootsOfUnitySheaf X N :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (rootsOfUnityPresheafIsoKernel X N)

/-- On sections the root/kernel comparison is the identity on actual roots. -/
lemma purityRootsPresheafKernelIso_sections (X : Scheme.{u}) (N : ℕ) (V : X.ProEtᵒᵖ)
    (x : (rootsOfUnityPresheafSheaf X N).obj.obj V) :
    proEtaleRootsOfUnitySections X N V
        ((purityRootsPresheafKernelIso X N).hom.hom.app V x) = x.down := by
  rw [purity_proEtaleRootsOfUnitySections_eq]
  change (Scheme.ProEt.rootsOfUnitySheafSectionsEquiv X N V.unop)
    ((Scheme.ProEt.rootsOfUnitySheafSectionsEquiv X N V.unop).symm x.down) = x.down
  exact AddEquiv.apply_symm_apply _ _

/-- The specified direct-image map has its defining projection formula. -/
lemma purity_rootDirectImage_sections {X Y : Scheme.{u}} (g : X ⟶ Y) (N : ℕ)
    (V : Y.ProEtᵒᵖ) (x : (proEtaleRootsOfUnitySheaf Y N).obj.obj V) :
    proEtaleRootsOfUnitySections X N ((proEtaleBaseChange g).op.obj V)
        ((proEtaleRootsOfUnityDirectImageMap g N).hom.app V x) =
      Additive.ofMul (restrictRootsOfUnity (pullback.fst V.unop.hom g).appTop.hom N
        (Additive.toMul (proEtaleRootsOfUnitySections Y N V x))) :=
  (existsUnique_proEtaleRootsOfUnityDirectImageMap g N).exists.choose_spec V x

/-- Both root models push a root forward by the same fibre-product projection. -/
lemma purityRootsPresheafKernelIso_lowerStar {X Y : Scheme.{u}} (g : X ⟶ Y) (N : ℕ) :
    (purityRootsPresheafKernelIso Y N).hom ≫ proEtaleRootsOfUnityDirectImageMap g N =
      rootsOfUnityToLowerStar g N ≫
        (g)_*[Ab.{u + 1}].map (purityRootsPresheafKernelIso X N).hom := by
  ext V x
  apply (proEtaleRootsOfUnitySections X N ((proEtaleBaseChange g).op.obj V)).injective
  change proEtaleRootsOfUnitySections X N _
      ((proEtaleRootsOfUnityDirectImageMap g N).hom.app V
        ((purityRootsPresheafKernelIso Y N).hom.hom.app V x)) =
    proEtaleRootsOfUnitySections X N _
      ((purityRootsPresheafKernelIso X N).hom.hom.app _
        ((rootsOfUnityToLowerStar g N).hom.app V x))
  have h₁ := purity_rootDirectImage_sections g N V
    ((purityRootsPresheafKernelIso Y N).hom.hom.app V x)
  have h₂ := congrArg (fun z : Additive (rootsOfUnity N Γ(V.unop.left, ⊤)) ↦
    Additive.ofMul (restrictRootsOfUnity (pullback.fst V.unop.hom g).appTop.hom N
      (Additive.toMul z))) (purityRootsPresheafKernelIso_sections Y N V x)
  have h₃ := purityRootsPresheafKernelIso_sections X N ((proEtaleBaseChange g).op.obj V)
    ((rootsOfUnityToLowerStar g N).hom.app V x)
  exact h₁.trans (h₂.trans h₃.symm)

/-- The canonical inverse-image root maps agree under the kernel comparison. -/
lemma purityRootsPresheafKernelIso_upperStar {X Y : Scheme.{u}} (g : X ⟶ Y) (N : ℕ) :
    (g)^*[Ab.{u + 1}].map (purityRootsPresheafKernelIso Y N).hom ≫
        proEtaleRootsOfUnityInverseImageMap g N =
      upperStarRootsOfUnityComparison g N ≫ (purityRootsPresheafKernelIso X N).hom := by
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_upperStarRootsOfUnityComparison]
  change (purityRootsPresheafKernelIso Y N).hom ≫
      (proEtaleSheafAdjunction g Ab.{u + 1}).homEquiv _ _
        (((proEtaleSheafAdjunction g Ab.{u + 1}).homEquiv _ _).symm
          (proEtaleRootsOfUnityDirectImageMap g N)) = _
  rw [Equiv.apply_symm_apply]
  exact purityRootsPresheafKernelIso_lowerStar g N

/-- The sheafified Tate-root pullback agrees with pullback of the kernel of the
power map. This identifies the datum used by integral Tate reduction. -/
lemma purity_rootsOfUnitySheafIsoKernel_upperStar {X Y : Scheme.{u}} (g : X ⟶ Y) (N : ℕ) :
    (g)^*[Ab.{u + 1}].map (rootsOfUnitySheafIsoKernel Y N).hom ≫
        proEtaleRootsOfUnityInverseImageMap g N =
      upperStarRootsOfUnitySheafHom g N ≫ (rootsOfUnitySheafIsoKernel X N).hom := by
  simp only [rootsOfUnitySheafIsoKernel, upperStarRootsOfUnitySheafHom,
    Iso.trans_hom, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun a ↦ (g)^*[Ab.{u + 1}].map (rootsOfUnitySheafIso Y N).hom ≫ a)
    (purityRootsPresheafKernelIso_upperStar g N)

end AlgebraicGeometry.ProEtale
