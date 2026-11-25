/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.FinitenessCriterionAux
public import WeilConjectures.ConstructibleSheaf.FilteredColimitStabilization
public import WeilConjectures.ConstructibleSheaf.FilteredColimit
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.MinimalCohomology

/-!
# Morphisms between constructible sheaves form a finite set

Let `k` be a separably closed field, `Λ` a finite ring whose exponent is invertible in `k`, and
`X` a separated scheme of finite type over `k`. For constructible étale sheaves `F` and `G` of
`Λ`-modules on `X`, the set of morphisms `F ⟶ G` is finite
(`AlgebraicGeometry.Etale.finite_hom_of_isConstructibleSheaf`): `F` is a quotient of a finite sum
of extensions by zero `v_! Λ` along affine étale `v : V ⟶ X` (Stacks 03SA and the stabilization of
filtered unions of subsheaves of a constructible sheaf), so `F ⟶ G` injects into a finite product
of the sections `G(V)`, which are finite by the finiteness of `RΓ(V, G)`.

In particular a group acting on a constructible sheaf acts through a finite quotient.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- Global sections of a constructible sheaf on a quasi-compact scheme locally of finite type over
a separably closed field form a finite set (finiteness of `H⁰(RΓ)`). -/
theorem finite_obj_etaleTerminal_of_isConstructibleSheaf {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q]
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf H] :
    Finite (H.obj.obj (op (etaleTerminal Y))) := by
  let K := (_root_.DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0).obj H
  have hd := boundedConstructible_rightDerivedLowerStar_of_finite Λ q (𝟙 _) q (Category.comp_id q)
    (DerivedCategory.boundedConstructible_singleFunctor_obj H 0)
  have hR := boundedFiniteCohomology_rightDerivedGlobalSections_of_rightDerivedLowerStar q hd
  have h₀ := ((_root_.DerivedCategory.boundedFiniteCohomology_iff_finite _).1 hR).2 0
  obtain ⟨e⟩ := nonempty_homology_rightDerivedGlobalSections_obj_iso_of_isGE Λ Y K 0
  exact @Finite.of_equiv _ _ h₀ (e ≪≫ (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso
    ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app H) ≪≫
    (Sheaf.ΓNatIsoSheafSections _ _ (isTerminalEtaleTerminal Y)).app _).toLinearEquiv.toEquiv

/-- Sections of a constructible sheaf over an affine étale `X`-scheme form a finite set. -/
theorem finite_obj_self_of_isConstructibleSheaf {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf G] {W : Scheme.{u}} [IsAffine W] (v : W ⟶ X) (h : Etale v) :
    Finite (G.obj.obj (op (Etale.self v h))) := by
  have := IsConstructibleSheaf.upperStar v G
  have := finite_obj_etaleTerminal_of_isConstructibleSheaf (v ≫ p)
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).obj G)
  exact @Finite.of_equiv _ _ this
    (((sheafSections _ _).obj (op (etaleTerminal W))).mapIso
      ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) v h).app G)
      ).toLinearEquiv.toEquiv

/-- **Morphisms between constructible sheaves form a finite set**: over a separated scheme of
finite type over a separably closed field, with coefficients a finite ring whose exponent is
invertible. -/
theorem finite_hom_of_isConstructibleSheaf {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    [IsConstructibleSheaf G] : Finite (F ⟶ G) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  obtain ⟨S, hS⟩ := exists_epi_ι_app_of_isConstructibleSheaf
    (isColimitFinsetSectionImageCocone F) (mono_finsetSectionImageCocone_ι_app F) ‹_›
  have hepi : Epi (finsetSigmaDesc (sectionGenerator F) (sectionGeneratorHom F) S) := by
    rw [← imageSubobject_arrow_comp
      (finsetSigmaDesc (sectionGenerator F) (sectionGeneratorHom F) S)]
    exact @epi_comp _ _ _ _ _ _ inferInstance _ hS
  have (i : S) : Finite (G.obj.obj (op (Etale.self i.1.1.1.hom i.1.1.1.prop))) :=
    have : IsAffine ((𝟭 Scheme).obj i.1.1.1.left) := i.1.1.2
    finite_obj_self_of_isConstructibleSheaf p G _ _
  refine Finite.of_injective (fun g (i : S) ↦ g.hom.app _ i.1.2) fun g g' hgg' ↦ ?_
  refine (cancel_epi (finsetSigmaDesc (sectionGenerator F) (sectionGeneratorHom F) S)).1 ?_
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  simp only [finsetSigmaDesc, Sigma.ι_comp_desc_assoc, sectionGeneratorHom, Etale.sectionHom_comp]
  exact congrArg _ (congrFun hgg' i)

end Etale

end AlgebraicGeometry
