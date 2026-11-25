/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Geometric stalks as inverse images

For a geometric point `s : Spec Ω ⟶ T` (`Ω` separably closed) of a scheme `T`, the stalk of an
étale sheaf of `Λ`-modules at `s` is the module of global sections of its inverse image along
`s`: the pointed étale neighbourhood `(Spec Ω, 𝟙)` of the tautological point of `Spec Ω` is
initial, so the stalk at the tautological point is the module of global sections.

## Main statements

- `AlgebraicGeometry.Etale.upperStarCompSectionsIsoSheafFiber` (`lem-kun-stalk-as-pullback`).
- `AlgebraicGeometry.Etale.sheafFiberHomologyIso` (`lem-kun-stalks-of-cohomology`).
- `AlgebraicGeometry.Etale.isZero_iff_forall_isZero_homology`
  (`lem-kun-d-zero-cohomology`).
- `AlgebraicGeometry.Etale.isIso_iff_forall_isIso_leftDerivedUpperStar_map`
  (`lem-kun-stalk-faithful-derived`).
- `AlgebraicGeometry.Etale.exists_comp_eq_sepClosureBaseChange`,
  `AlgebraicGeometry.Etale.isIso_iff_isIso_upperStar_sepClosureBaseChange_map` and
  `AlgebraicGeometry.Etale.isIso_iff_isIso_leftDerivedUpperStar_sepClosureBaseChange_map`
  (`lem-kun-sep-closure-conservative`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section TautologicalPoint

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The tautological pointed étale neighbourhood `(Spec Ω, 𝟙)` of the geometric point
`𝟙 : Spec Ω ⟶ Spec Ω`. -/
noncomputable abbrev tautologicalElement :
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.Elements :=
  Functor.elementsMk _ (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
    (Over.homMk (𝟙 (Spec (.of Ω))) (Category.comp_id _))


/-- The tautological pointed étale neighbourhood `(Spec Ω, 𝟙)` is initial among the pointed
étale neighbourhoods of the geometric point `𝟙 : Spec Ω ⟶ Spec Ω`: a pointed neighbourhood
`(V, x)` receives the unique morphism `x : Spec Ω ⟶ V`. -/
noncomputable def isInitialTautologicalElement : IsInitial (tautologicalElement (Ω := Ω)) :=
  IsInitial.ofUniqueHom
    (fun Y ↦ ⟨MorphismProperty.Over.homMk Y.2.left (by simpa using Over.w Y.2), by
      apply Over.OverMorphism.ext
      simp [pointSmallEtale, Etale.forget]⟩)
    (fun Y m ↦ by
      refine Functor.Elements.hom_ext ?_
      apply MorphismProperty.Over.Hom.ext
      have := congrArg CommaMorphism.left m.2
      simpa [pointSmallEtale, Etale.forget] using this)

/-- The germ map from the sections over the tautological neighbourhood to the stalk at the
tautological point of `Spec Ω` is an isomorphism. -/
instance isIso_toPresheafFiber_tautological
    (P : (Spec (.of Ω)).Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :
    IsIso ((pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber tautologicalElement.1
      tautologicalElement.2 P) :=
  isIso_ι_of_isTerminal isInitialTautologicalElement.op _

/-- The germ map at the tautological point of `Spec Ω`, as a natural transformation from the
global sections to the stalk. -/
noncomputable def sectionsToSheafFiberTautological :
    (sheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))) ⟶
      (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber :=
  Functor.whiskerLeft (sheafToPresheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    ((pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiberNatTrans tautologicalElement.1
      tautologicalElement.2)

instance : IsIso (sectionsToSheafFiberTautological Λ (Ω := Ω)) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
    (fun X ↦ isIso_toPresheafFiber_tautological Λ X.obj)

/-- The stalk at the tautological point of `Spec Ω` is the module of global sections. -/
noncomputable def sectionsIsoSheafFiberTautological :
    (sheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))) ≅
      (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber :=
  asIso (sectionsToSheafFiberTautological Λ)

end TautologicalPoint

section Pullback

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Blueprint `lem-kun-stalk-as-pullback`: **a stalk is the inverse image to a geometric
point.** For a geometric point `s : Spec Ω ⟶ T` the stalk of an étale sheaf `F` of
`Λ`-modules at `s` is the module of global sections of the inverse image `s^* F`, naturally
in `F`: the stalk of `s^* F` at the tautological point of `Spec Ω` is that of `F` at `s`
(`AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`), and is the module of global sections
of `s^* F` (`AlgebraicGeometry.Etale.sectionsIsoSheafFiberTautological`). -/
noncomputable def upperStarCompSectionsIsoSheafFiber {T : Scheme.{u}}
    (s : Spec (.of Ω) ⟶ T) :
    (s)^*[ModuleCat.{u + 1} Λ] ⋙
        (sheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))) ≅
      (pointSmallEtale s).sheafFiber :=
  Functor.isoWhiskerLeft _ (sectionsIsoSheafFiberTautological Λ) ≪≫
    upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) s (𝟙 _) ≪≫
    eqToIso (by rw [Category.id_comp])

/-- Blueprint `lem-kun-stalks-of-cohomology`: **stalks of cohomology sheaves.** For
`Q ∈ D(T_ét, Λ)` and a geometric point `s : Spec Ω ⟶ T`, the stalk of `ℋ^q(Q)` at `s` is
the module of global sections of `ℋ^q(Ls^* Q)`, that is, `ℋ^q(Q)_s ≅ ℋ^q(Q_s)`: the stalk is
the inverse image (`lem-kun-stalk-as-pullback`), and the exact functor `s^*` commutes with
`ℋ^q` (`AlgebraicGeometry.Etale.leftDerivedUpperStarHomologyFunctorIso`). -/
noncomputable def sheafFiberHomologyIso {T : Scheme.{u}} (s : Spec (.of Ω) ⟶ T)
    (Q : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (q : ℤ) :
    (pointSmallEtale s).sheafFiber.obj ((_root_.DerivedCategory.homologyFunctor _ q).obj Q) ≅
      ((sheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))).obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((L((s)^*[ModuleCat.{u + 1} Λ])).obj Q)) :=
  ((upperStarCompSectionsIsoSheafFiber Λ s).app _).symm ≪≫
    ((sheafSections _ _).obj _).mapIso
      ((leftDerivedUpperStarHomologyFunctorIso (ModuleCat.{u + 1} Λ) s q).app Q)

end Pullback

/-- Blueprint `lem-kun-d-zero-cohomology`: **objects with vanishing cohomology.** An object
`E ∈ D(T_ét, Λ)` is zero if and only if all its cohomology sheaves `ℋ^q(E)` are zero. -/
theorem isZero_iff_forall_isZero_homology {T : Scheme.{u}}
    (E : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsZero E ↔ ∀ q : ℤ, IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj E) :=
  _root_.DerivedCategory.isZero_iff E

/-- Blueprint `lem-kun-stalk-faithful-derived`: **stalk faithfulness for derived objects.**
A morphism `φ` of `D(T_ét, Λ)` is an isomorphism if and only if its derived pullback
`Ls^* φ` to every geometric point `s : Spec Ω ⟶ T` is an isomorphism. It suffices to test the
geometric points given by algebraic closures of the residue fields
(`AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map`). -/
theorem isIso_iff_forall_isIso_leftDerivedUpperStar_map {T : Scheme.{u}}
    {M N : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ N) :
    IsIso φ ↔ ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T),
      IsIso ((L((s)^*[ModuleCat.{u + 1} Λ])).map φ) :=
  ⟨fun _ _ _ _ _ ↦ inferInstance, fun h ↦
    isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map Λ φ fun _ ↦ h _ _⟩

section SepClosure

variable {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))

/-- The base change `X_{K^sep} ⟶ X` of a `K`-scheme `X` (with structure morphism `p`) to the
separable closure `K^sep` of `K`. -/
noncomputable abbrev sepClosureBaseChange :
    pullback p (Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))) ⟶ X :=
  pullback.fst _ _

instance surjective_spec_map_algebraMap_separableClosure :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))) :=
  ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩

/-- Blueprint `lem-kun-sep-closure-conservative` (first part): every geometric point of a
`K`-scheme `X` factors through `X_{K^sep}`: a separably closed field extension of `K` receives
a `K`-embedding of `K^sep`. -/
theorem exists_comp_eq_sepClosureBaseChange {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) : ∃ t, t ≫ sepClosureBaseChange p = s := by
  let := (Spec.preimage (s ≫ p)).hom.toAlgebra
  let ψ : SeparableClosure K →ₐ[K] Ω := IsSepClosed.lift
  refine ⟨pullback.lift s (Spec.map (CommRingCat.ofHom ψ.toRingHom)) ?_,
    pullback.lift_fst _ _ _⟩
  rw [← Spec.map_comp, ← Spec.map_preimage (s ≫ p)]
  congr 1
  ext x
  exact (ψ.commutes x).symm

/-- Blueprint `lem-kun-sep-closure-conservative`: **conservativity of base change to a
separable closure, for sheaves.** A morphism of étale sheaves of `Λ`-modules on a `K`-scheme
`X` is an isomorphism if and only if its pullback to `X_{K^sep}` is: `X_{K^sep} ⟶ X` is
surjective, being a base change of the surjective `Spec K^sep ⟶ Spec K`. -/
theorem isIso_iff_isIso_upperStar_sepClosureBaseChange_map
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G) :
    IsIso φ ↔ IsIso ((sepClosureBaseChange p)^*[ModuleCat.{u + 1} Λ].map φ) := by
  refine ⟨fun _ ↦ inferInstance, fun h ↦ ?_⟩
  refine isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ) (ι := PUnit)
    (fun _ ↦ sepClosureBaseChange p) (fun x ↦ ?_) φ fun _ ↦ h
  obtain ⟨y, hy⟩ := (sepClosureBaseChange p).surjective x
  exact ⟨⟨⟩, y, hy⟩

/-- Blueprint `lem-kun-sep-closure-conservative`: **conservativity of base change to a
separable closure, for derived objects.** A morphism of `D(X_ét, Λ)` is an isomorphism if and
only if its derived pullback to `X_{K^sep}` is: on cohomology sheaves this is the statement
for sheaves, the pullback being exact. -/
theorem isIso_iff_isIso_leftDerivedUpperStar_sepClosureBaseChange_map
    {M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ N) :
    IsIso φ ↔ IsIso ((L((sepClosureBaseChange p)^*[ModuleCat.{u + 1} Λ])).map φ) := by
  refine ⟨fun _ ↦ inferInstance, fun h ↦ ?_⟩
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  have := h
  rw [isIso_iff_isIso_upperStar_sepClosureBaseChange_map Λ p]
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarHomologyFunctorIso _ _ n) φ).2
    (Functor.map_isIso (_root_.DerivedCategory.homologyFunctor _ n)
      ((L((sepClosureBaseChange p)^*[ModuleCat.{u + 1} Λ])).map φ))

end SepClosure

end Etale

end AlgebraicGeometry
