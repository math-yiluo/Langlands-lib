/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite
namespace AlgebraicGeometry.RingedSpace

/-- Forgetting global scalars identifies module cohomology with open module cohomology
at the whole space, naturally in the module sheaf.

Source: Stacks Project, Cohomology, Tag 01DZ, the injective-module-resolution definition
of cohomology; the exact forgetful functor preserves homology.
(blueprint: lem-weil-pbc-module-cohomology-top-comparison).

Proof: Global sections followed by forgetting scalars is naturally identical to
`openModuleSections X ⊤`: both evaluate the underlying module presheaf at the top open
and forget its scalar action. Use the same injective resolution of each module sheaf
for both derived functors. Forgetting scalars preserves kernels and cokernels, so its
application to the homology of the global-sections complex is canonically the homology
of that complex after forgetting scalars. This last complex is the top-open-sections
complex. Compose this homology comparison with the two injective-resolution comparisons
to obtain the displayed isomorphism on each object. A lift of any sheaf morphism to its
injective resolutions commutes with evaluation and scalar forgetting; naturality of
the homology comparison and the resolution comparisons therefore makes these object
isomorphisms a natural isomorphism. Homotopic choices of lifts give the same homology
map, so the construction is independent of the lift. This works in degree zero and
for the empty ringed space, and requires no compactness hypothesis. -/
theorem nonempty_moduleCohomology_top_iso (X : RingedSpace.{u}) (p : ℕ) :
    Nonempty ((moduleCohomology X p ⋙
      forget₂ (ModuleCat.{u} ((moduleRings X).obj.obj (op ⊤))) AddCommGrpCat.{u}) ≅
      openModuleCohomology X p ⊤) := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X)) :=
    (moduleSheaves_abelian_enoughInjectives X).2
  let M := ModuleCat.{u} ((moduleRings X).obj.obj (op ⊤))
  let U : M ⥤ AddCommGrpCat.{u} := forget₂ M AddCommGrpCat.{u}
  let c := ComplexShape.up ℕ
  let h : U.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor _ c p ≅
      HomologicalComplex.homologyFunctor M c p ⋙ U :=
    Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor M c p)
      (ShortComplex.homologyFunctorIso U)
  let k : U.mapHomotopyCategory c ⋙ HomotopyCategory.homologyFunctor _ c p ≅
      HomotopyCategory.homologyFunctor M c p ⋙ U :=
    Quotient.natIsoLift _
      (Functor.isoWhiskerRight (U.mapHomotopyCategoryFactors c) _ ≪≫
        Functor.isoWhiskerLeft (U.mapHomologicalComplex c)
          (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{u} c p) ≪≫
        h ≪≫ Functor.isoWhiskerRight (HomotopyCategory.homologyFunctorFactors M c p).symm U)
  let G := globalSectionsFunctor X
  let s : G ⋙ U ≅ openModuleSections X ⊤ := Iso.refl _
  exact ⟨Functor.isoWhiskerLeft (injectiveResolutions _) (Functor.isoWhiskerLeft
      (G.mapHomotopyCategory c) k.symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso s c) _)⟩

end AlgebraicGeometry.RingedSpace
