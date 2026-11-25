/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.IhomUnitTensor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.Algebra.Homology.Monoidal.ProjectionMap

/-!
# Perfect complexes on the coefficient site

A complex `K` of étale sheaves of `Λ`-modules on `X` is *perfect on the coefficient site*
(blueprint `def-weil-site-perfect-complex`) if, on the members `U ⟶ X` of some étale cover,
its restriction `K|_U` is isomorphic to a bounded complex of finite projective `Λ_U`-modules,
a finite projective module being a direct summand of a finite sum `Λ_U^{⊕m}` of copies of the
constant sheaf.

## Implementation notes

The blueprint works on the small pro-étale site; the definition is stated here on the small
étale site of the étale model of the coefficient categories, the restriction to `U` being the
derived pullback `Lu^*` along the member `u : U ⟶ X` of the cover. A direct summand of
`Λ_U^{⊕m}` is a retract of the constant sheaf with value `Λ^m`. The coefficient ring is
arbitrary: for `Λ = A_{E,n}` this is the finite stage of the blueprint, and for `Λ = 𝒪_E` it
is the integral stage in the étale model. Elsewhere in the repository perfectness is rendered as
dualizability for the derived tensor product
(`WeilConjectures.SixFunctors.Etale.Derived.Perfect`).

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.IsSitePerfect`: perfectness on the coefficient site.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- Blueprint `def-weil-site-perfect-complex`: Perfect complexes on the coefficient site.

An object `K` of `D(X_ét, Λ)` is *perfect on the coefficient site* if there is an étale cover
`{uᵢ : Uᵢ ⟶ X}` such that each restriction `Luᵢ^* K` is isomorphic to (the image in
`D(Uᵢ, Λ)` of) a bounded complex `P` of sheaves of `Λ`-modules on `Uᵢ` whose terms are finite
projective, i.e. retracts of the constant sheaf `(Λ^m)_{Uᵢ}` for some `m`. -/
def DerivedCategory.IsSitePerfect
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) : Prop :=
  ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀,
    ∃ (P : CochainComplex (Sheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ n, ∃ m : ℕ, Nonempty (Retract (P.X n)
        ((constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin m → Λ))))) ∧
      Nonempty ((L((𝒰.f i)^*[ModuleCat.{u + 1} Λ])).obj K ≅ DerivedCategory.Q.obj P)

/-- Perfectness on the coefficient site is invariant under isomorphism. -/
lemma DerivedCategory.IsSitePerfect.of_iso
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (e : K ≅ K')
    (hK : DerivedCategory.IsSitePerfect K) : DerivedCategory.IsSitePerfect K' := by
  obtain ⟨𝒰, h⟩ := hK
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨P, a, b, ha, hb, hP, ⟨e'⟩⟩ := h i
  exact ⟨P, a, b, ha, hb, hP, ⟨(L((𝒰.f i)^*[ModuleCat.{u + 1} Λ])).mapIso e.symm ≪≫ e'⟩⟩

section General

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {Y : Scheme.{u}}

/-- For a dualizable `K`, the internal hom out of `K` commutes with tensoring by any `T`:
`RHom(K, M ⊗ᴸ T) ≅ RHom(K, M) ⊗ᴸ T`, both sides being `K^∨ ⊗ᴸ M ⊗ᴸ T`
(`AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_coefficientDual_tensor`). -/
theorem DerivedCategory.nonempty_iso_derivedHom_derivedTensor_of_isDualizable
    {K : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (hK : IsDualizable K)
    (M T : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    Nonempty ((RHom(Y)[A].obj (op K)).obj (((derivedTensor A Y).obj M).obj T) ≅
      ((derivedTensor A Y).obj ((RHom(Y)[A].obj (op K)).obj M)).obj T) := by
  obtain ⟨e₁⟩ := DerivedCategory.nonempty_iso_coefficientDual_tensor hK (M ⊗ T)
  obtain ⟨e₂⟩ := DerivedCategory.nonempty_iso_coefficientDual_tensor hK M
  exact ⟨e₁.symm ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso e₂ T⟩

end General

section Reduction

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {Y : Scheme.{u}}

/-- Dualizability in `D(Y_ét)`, with the monoidal structure of a general coefficient category.
Stated through this abbreviation, statements about `A = ModuleCat Λ` use the same monoidal
instance as the general results they are deduced from. -/
abbrev DerivedCategory.IsDualizableEtale (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    Prop :=
  IsDualizable K

/-- The comparison `RHom(K, Λ_Y) ⊗ᴸ K ⟶ RHom(K, K)` in `D(Y_ét)`, for a general coefficient
category. -/
noncomputable abbrev DerivedCategory.ihomUnitTensorToIhomEtale
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (ihom K).obj (𝟙_ _) ⊗ K ⟶ (ihom K).obj K :=
  MonoidalClosed.ihomUnitTensorToIhom K K

/-- Dualizability of an étale sheaf, with the monoidal structure of a general coefficient
category (compare `AlgebraicGeometry.Etale.DerivedCategory.IsDualizableEtale`). -/
abbrev IsDualizableSheaf (F : Sheaf Y.smallEtaleTopology A) : Prop :=
  IsDualizable F

/-- A bounded complex of dualizable sheaves is dualizable in `D(Y_ét)`
(`DerivedCategory.isDualizable_Q_obj`). -/
theorem DerivedCategory.isDualizableEtale_Q_obj
    (P : CochainComplex (Sheaf Y.smallEtaleTopology A) ℤ) (a b : ℤ) [P.IsStrictlyGE a]
    [P.IsStrictlyLE b] (hP : ∀ n, IsDualizableSheaf (P.X n)) :
    DerivedCategory.IsDualizableEtale (_root_.DerivedCategory.Q.obj P) :=
  _root_.DerivedCategory.isDualizable_Q_obj P a b hP

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A] in
lemma IsDualizableSheaf.of_retract {F G : Sheaf Y.smallEtaleTopology A} (h : Retract F G)
    (hG : IsDualizableSheaf G) : IsDualizableSheaf F :=
  IsDualizable.of_retract h hG

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A] in
lemma IsDualizableSheaf.of_iso {F G : Sheaf Y.smallEtaleTopology A} (e : F ≅ G)
    (hF : IsDualizableSheaf F) : IsDualizableSheaf G :=
  IsDualizable.of_iso e hF

omit [Abelian.HasFunctorialFlatResolution A] in
lemma IsDualizableSheaf.biprod {F G : Sheaf Y.smallEtaleTopology A} (hF : IsDualizableSheaf F)
    (hG : IsDualizableSheaf G) : IsDualizableSheaf (F ⊞ G) :=
  IsDualizable.biprod hF hG

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A] in
lemma isDualizableSheaf_of_isZero {F : Sheaf Y.smallEtaleTopology A} (hF : IsZero F) :
    IsDualizableSheaf F :=
  CategoryTheory.IsZero.isDualizable hF

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A] in
lemma isDualizableSheaf_unit : IsDualizableSheaf (𝟙_ (Sheaf Y.smallEtaleTopology A)) :=
  isDualizable_unit

/-- An object `K` of `D(Y_ét)` is dualizable as soon as the comparison
`RHom(K, Λ_Y) ⊗ᴸ K ⟶ RHom(K, K)` is an isomorphism: `RHom(K, Λ_Y)` is then a left dual of `K`
(`CategoryTheory.MonoidalClosed.exactPairingOfIsIso`), hence also a right dual, the derived
tensor product being symmetric. -/
theorem DerivedCategory.isDualizable_of_isIso_ihomUnitTensorToIhom
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    [IsIso (MonoidalClosed.ihomUnitTensorToIhom K K)] : IsDualizable K := by
  let := MonoidalClosed.exactPairingOfIsIso K
  obtain ⟨_⟩ := DerivedCategory.nonempty_exactPairing_swap ((ihom K).obj (𝟙_ _)) K
  exact ⟨⟨(ihom K).obj (𝟙_ _)⟩⟩

variable
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [instF : ∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [instC : ConcreteCategory.{u + 1} A FC]
  [instR : (CategoryTheory.forget A).ReflectsIsomorphisms]
  [instP : PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [instS : Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include instF instC instR instP instS

/-- **Restrictions to an étale cover jointly reflect isomorphisms in `D(Y_ét)`**: a morphism
whose derived pullbacks to the members of an étale cover are isomorphisms is an isomorphism,
since the pullbacks commute with the cohomology sheaves and restrictions of sheaves along a
jointly surjective family reflect isomorphisms
(`AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective`). -/
theorem DerivedCategory.isIso_of_isIso_leftDerivedUpperStar_map_of_cover
    (𝒰 : Cover.{u} etalePrecoverage Y) {M N : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (φ : M ⟶ N) (h : ∀ i, IsIso ((L((𝒰.f i)^*[A])).map φ)) : IsIso φ := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective A 𝒰.f
    (fun x ↦ ?_) _ fun i ↦ ?_
  · exact 𝒰.exists_eq x
  · have := h i
    exact (NatIso.isIso_map_iff (leftDerivedUpperStarHomologyFunctorIso A (𝒰.f i) n) φ).2
      (inferInstanceAs (IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map
        ((L((𝒰.f i)^*[A])).map φ))))

/-- An object of `D(Y_ét)` is dualizable if, on the members of some étale cover, the derived
pullback of the comparison `RHom(K, Λ_Y) ⊗ᴸ K ⟶ RHom(K, K)` is an isomorphism. -/
theorem DerivedCategory.isDualizable_of_cover (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (𝒰 : Cover.{u} etalePrecoverage Y)
    (h : ∀ i, IsIso ((L((𝒰.f i)^*[A])).map (DerivedCategory.ihomUnitTensorToIhomEtale K))) :
    DerivedCategory.IsDualizableEtale K :=
  have := DerivedCategory.isIso_of_isIso_leftDerivedUpperStar_map_of_cover 𝒰 _ h
  DerivedCategory.isDualizable_of_isIso_ihomUnitTensorToIhom K

end Reduction

/-- The constant sheaf `(Λ^m)_U` is dualizable: it is a finite biproduct of copies of the unit
sheaf `Λ_U` (`CategoryTheory.IsDualizable.biprod`). -/
theorem isDualizableSheaf_constantSheaf_pi {U : Scheme.{u}} (m : ℕ) :
    IsDualizableSheaf ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ (Fin m → Λ))) := by
  have := (constantSheafAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    terminalIsTerminal).isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0}
      (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (constantSheafAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      terminalIsTerminal).leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  induction m with
  | zero =>
    exact isDualizableSheaf_of_isZero (Functor.map_isZero _ (ModuleCat.isZero_of_subsingleton _))
  | succ m ih =>
    let e : ModuleCat.of Λ (Fin (m + 1) → Λ) ≅
        ModuleCat.of Λ Λ ⊞ ModuleCat.of Λ (Fin m → Λ) :=
      (Fin.consLinearEquiv Λ (fun _ : Fin (m + 1) ↦ Λ)).symm.toModuleIso ≪≫
        (ModuleCat.biprodIsoProd (ModuleCat.of Λ Λ) (ModuleCat.of Λ (Fin m → Λ))).symm
    refine IsDualizableSheaf.of_iso ((constantSheaf _ _).mapIso e ≪≫
      Functor.mapBiprod (constantSheaf _ _) _ _).symm ?_
    exact IsDualizableSheaf.biprod isDualizableSheaf_unit ih

/-- An object of `D(U_ét, Λ)` isomorphic to a bounded complex of finite projective `Λ_U`-modules
is dualizable (`CategoryTheory.IsDualizable.of_retract`,
`AlgebraicGeometry.Etale.isDualizableSheaf_constantSheaf_pi`). -/
theorem isDualizableEtale_of_trivialization {U : Scheme.{u}}
    {M : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hP : ∀ n, ∃ m : ℕ, Nonempty (Retract (P.X n)
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Fin m → Λ)))))
    (e : M ≅ DerivedCategory.Q.obj P) : DerivedCategory.IsDualizableEtale M :=
  (DerivedCategory.isDualizableEtale_Q_obj P a b fun n ↦
    have h := hP n
    IsDualizableSheaf.of_retract h.choose_spec.some
      (isDualizableSheaf_constantSheaf_pi h.choose)).of_iso e.symm

section Projection

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

/-- Transposing a projection map gives the tensor comparison preceded by the unit. -/
private theorem unit_app_map_projectionMap
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
    {L : D ⥤ C} {R : C ⥤ D} [R.Monoidal] (adj : L ⊣ R) (K : C) (T : D) :
    adj.unit.app (R.obj K ⊗ T) ≫ R.map ((Functor.Monoidal.projectionMap adj K).app T) =
      R.obj K ◁ adj.unit.app T ≫ Functor.LaxMonoidal.μ R K (L.obj T) :=
  (adj.homEquiv _ _).apply_symm_apply _

/-- Projection maps commute with a lax monoidal square whose adjunction units agree. -/
private theorem projectionMap_laxSquare
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']
    {L : D ⥤ C} {R : C ⥤ D} {L' : D' ⥤ C'} {R' : C' ⥤ D'}
    [R'.Monoidal] (adj : L ⊣ R) (adj' : L' ⊣ R')
    (QC : C ⥤ C') (QD : D ⥤ D') [QC.LaxMonoidal] [QD.LaxMonoidal]
    (e : QC ⋙ R' ≅ R ⋙ QD) (ν : QD ⋙ L' ⟶ L ⋙ QC) (K : C) (T : D)
    (m : R.obj K ⊗ R.obj (L.obj T) ⟶ R.obj (K ⊗ L.obj T))
    (p : L.obj (R.obj K ⊗ T) ⟶ K ⊗ L.obj T)
    (hμ : Functor.LaxMonoidal.μ R' (QC.obj K) (QC.obj (L.obj T)) ≫
        R'.map (Functor.LaxMonoidal.μ QC K (L.obj T)) ≫ e.hom.app (K ⊗ L.obj T) =
      (e.hom.app K ⊗ₘ e.hom.app (L.obj T)) ≫
        Functor.LaxMonoidal.μ QD (R.obj K) (R.obj (L.obj T)) ≫ QD.map m)
    (hunit : ∀ T, adj'.unit.app (QD.obj T) ≫ R'.map (ν.app T) ≫ e.hom.app (L.obj T) =
      QD.map (adj.unit.app T))
    (hπ : adj.unit.app _ ≫ R.map p = R.obj K ◁ adj.unit.app T ≫ m) :
    L'.map (e.hom.app K ▷ QD.obj T ≫ Functor.LaxMonoidal.μ QD (R.obj K) T) ≫
        ν.app (R.obj K ⊗ T) ≫ QC.map p =
      (Functor.Monoidal.projectionMap adj' (QC.obj K)).app (QD.obj T) ≫
        QC.obj K ◁ ν.app T ≫ Functor.LaxMonoidal.μ QC K (L.obj T) := by
  have hπ' := unit_app_map_projectionMap adj' (QC.obj K) (QD.obj T)
  have hn : R'.map (QC.map p) ≫ e.hom.app (K ⊗ L.obj T) =
      e.hom.app (L.obj (R.obj K ⊗ T)) ≫ QD.map (R.map p) := e.hom.naturality p
  apply (adj'.homEquiv _ _).injective
  apply (cancel_mono (e.hom.app (K ⊗ L.obj T))).1
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [adj'.unit_naturality_assoc, adj'.unit_naturality_assoc, hn,
    reassoc_of% (hunit (R.obj K ⊗ T)), ← QD.map_comp, hπ, QD.map_comp,
    ← Functor.LaxMonoidal.μ_natural_right_assoc]
  erw [reassoc_of% hπ']
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  erw [hμ]
  simp only [tensorHom_def, Functor.comp_obj, Category.assoc]
  erw [whisker_exchange_assoc, whisker_exchange_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [Category.assoc]
  erw [hunit]

/-- The derived adjunction `D(u_!) ⊣ Lu^*` for an étale morphism `u`, with the right adjoint
the left derived functor `Lu^*` (isomorphic to the levelwise `D(u^*)`, `u^*` being exact). -/
noncomputable def derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction {U : Scheme.{u}}
    (f : U ⟶ X) [Etale f] :
    (Etale.etaleLowerShriek A f inferInstance).mapDerivedCategory ⊣ L((f)^*[A]) :=
  let _ : CatCommSq ((Etale.etaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh
      (Etale.etaleLowerShriek A f inferInstance).mapDerivedCategory :=
    ⟨(Etale.etaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.symm⟩
  let _ : CatCommSq (((f)^*[A]).mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh
      DerivedCategory.Qh L((f)^*[A]) :=
    ⟨(asIso ((f)^*[A]).leftDerivedFunctorCounit).symm⟩
  ((Etale.etaleLowerShriekUpperStarAdjunction A f inferInstance).mapHomotopyCategory
    (.up ℤ)).localization DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _ _

omit [HasSmallSiteSheafify A] in
open HomotopyCategory _root_.DerivedCategory in
/-- On objects coming from cochain complexes, the derived projection map of `D(u_!) ⊣ Lu^*` is
the image of the projection map on cochain complexes, up to the tensor comparison maps of `Qh`. -/
lemma projectionMap_derivedEtaleLowerShriek_app_Qh {U : Scheme.{u}} (f : U ⟶ X) [Etale f]
    [(f)^*[A].PreservesFlat] (K₁ : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ)
    (T₁ : CochainComplex (Sheaf U.smallEtaleTopology A) ℤ) :
    letI := leftDerivedUpperStarMonoidal A f
    (Functor.Monoidal.projectionMap (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction
        (A := A) f) (Qh.obj ((quotient _ _).obj K₁))).app (Qh.obj ((quotient _ _).obj T₁)) ≫
      (Qh.obj ((quotient _ _).obj K₁) ◁
        (Etale.etaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.hom.app
          ((quotient _ _).obj T₁)) ≫
      Functor.LaxMonoidal.μ Qh ((quotient _ _).obj K₁)
        (((Etale.etaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁)) =
    (Etale.etaleLowerShriek A f inferInstance).mapDerivedCategory.map
        (((f)^*[A].leftDerivedFunctorCounit.app ((quotient _ _).obj K₁) ▷
          Qh.obj ((quotient _ _).obj T₁)) ≫
          Functor.LaxMonoidal.μ Qh _ ((quotient _ _).obj T₁)) ≫
      (Etale.etaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.hom.app _ ≫
        Qh.map ((quotient _ _).map ((Functor.Monoidal.projectionMap
          ((Etale.etaleLowerShriekUpperStarAdjunction A f inferInstance).mapHomologicalComplex
            (.up ℤ)) K₁).app T₁)) := by
  let := leftDerivedUpperStarMonoidal A f
  have hμ : Functor.LaxMonoidal.μ L((f)^*[A]) (Qh.obj ((quotient _ _).obj K₁))
        (Qh.obj (((Etale.etaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁))) ≫
      L((f)^*[A]).map (Functor.LaxMonoidal.μ Qh ((quotient _ _).obj K₁)
        (((Etale.etaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁))) ≫
      (f)^*[A].leftDerivedFunctorCounit.app ((quotient _ _).obj K₁ ⊗
        ((Etale.etaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁)) =
      ((f)^*[A].leftDerivedFunctorCounit.app ((quotient _ _).obj K₁) ⊗ₘ
        (f)^*[A].leftDerivedFunctorCounit.app
          (((Etale.etaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
            ((quotient _ _).obj T₁))) ≫
      Functor.LaxMonoidal.μ Qh (((f)^*[A].mapHomotopyCategory (.up ℤ)).obj ((quotient _ _).obj K₁))
        (((f)^*[A].mapHomotopyCategory (.up ℤ)).obj
          (((Etale.etaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
            ((quotient _ _).obj T₁))) ≫
      Qh.map ((quotient _ _).map (Functor.LaxMonoidal.μ ((f)^*[A].mapHomologicalComplex (.up ℤ)) K₁
        (((Etale.etaleLowerShriek A f inferInstance).mapHomologicalComplex (.up ℤ)).obj T₁))) := by
    have h := leftDerivedUpperStarTensorComparison_app_app_comp A f ((quotient _ _).obj K₁)
      (((Etale.etaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
        ((quotient _ _).obj T₁))
    rw [← cancel_epi (Functor.OplaxMonoidal.δ L((f)^*[A]) _ _), Functor.Monoidal.δ_μ_assoc]
    erw [reassoc_of% h]
    rw [← Functor.map_comp _root_.DerivedCategory.Qh]
    have hδ : Functor.OplaxMonoidal.δ ((f)^*[A].mapHomotopyCategory (.up ℤ)) ((quotient _ _).obj K₁)
        (((Etale.etaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁)) ≫
        (quotient _ _).map (Functor.LaxMonoidal.μ ((f)^*[A].mapHomologicalComplex (.up ℤ)) K₁
          (((Etale.etaleLowerShriek A f inferInstance).mapHomologicalComplex (.up ℤ)).obj T₁)) =
        𝟙 _ := by
      change (quotient _ _).map (Functor.OplaxMonoidal.δ ((f)^*[A].mapHomologicalComplex (.up ℤ))
        K₁ (((Etale.etaleLowerShriek A f inferInstance).mapHomologicalComplex (.up ℤ)).obj T₁)) ≫
        _ = _
      rw [← Functor.map_comp, Functor.Monoidal.δ_μ]
      exact CategoryTheory.Functor.map_id _ _
    erw [hδ, CategoryTheory.Functor.map_id]
    rw [Category.comp_id]
  have hunit (T : HomotopyCategory (Sheaf U.smallEtaleTopology A) (.up ℤ)) :
      (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction (A := A) f).unit.app (Qh.obj T) ≫
        L((f)^*[A]).map
          ((Etale.etaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.hom.app T) ≫
        (f)^*[A].leftDerivedFunctorCounit.app
          (((Etale.etaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj T) =
      Qh.map (((Etale.etaleLowerShriekUpperStarAdjunction A f inferInstance).mapHomotopyCategory
        (.up ℤ)).unit.app T) := by
    rw [derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction, Adjunction.localization_unit_app]
    dsimp only [CatCommSq.iso, Iso.symm_hom, asIso_inv]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    rw [Category.id_comp, NatIso.isIso_inv_app, IsIso.inv_hom_id, Category.comp_id]
  have hc := unit_app_map_projectionMap
    ((Etale.etaleLowerShriekUpperStarAdjunction A f inferInstance).mapHomologicalComplex (.up ℤ))
    K₁ T₁
  apply Eq.symm
  refine projectionMap_laxSquare
    ((Etale.etaleLowerShriekUpperStarAdjunction A f inferInstance).mapHomotopyCategory (.up ℤ))
    (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction (A := A) f) Qh Qh
    (asIso (f)^*[A].leftDerivedFunctorCounit)
    (Etale.etaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.hom
    ((quotient _ _).obj K₁) ((quotient _ _).obj T₁) _ _ hμ hunit ?_
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_unit_app_quotient, Functor.mapHomotopyCategory_map,
    ← HomotopyCategory.MonoidalCategory.quotient_map_whiskerLeft']
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact (quotient _ _).congr_map hc

open HomotopyCategory _root_.DerivedCategory in
omit [HasSmallSiteSheafify A] in
/-- The derived projection map of `D(u_!) ⊣ Lu^*` is an isomorphism at `K = Qh K₁` when `K₁`
and `u^*K₁` are K-flat and the projection maps on cochain complexes are isomorphisms. -/
lemma isIso_projectionMap_derivedEtaleLowerShriek_app_Qh {U : Scheme.{u}} (f : U ⟶ X)
    [Etale f] [(f)^*[A].PreservesFlat] (K₁ : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ)
    (hK₁ : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ((quotient _ _).obj K₁))
    (hK₁' : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
      ((quotient _ _).obj (((f)^*[A].mapHomologicalComplex (.up ℤ)).obj K₁)))
    (T₁ : CochainComplex (Sheaf U.smallEtaleTopology A) ℤ)
    [IsIso ((Functor.Monoidal.projectionMap
      ((Etale.etaleLowerShriekUpperStarAdjunction A f inferInstance).mapHomologicalComplex
        (.up ℤ)) K₁).app T₁)] :
    letI := leftDerivedUpperStarMonoidal A f
    IsIso ((Functor.Monoidal.projectionMap (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction
        (A := A) f) (Qh.obj ((quotient _ _).obj K₁))).app (Qh.obj ((quotient _ _).obj T₁))) := by
  let := leftDerivedUpperStarMonoidal A f
  have h := projectionMap_derivedEtaleLowerShriek_app_Qh (A := A) f K₁ T₁
  have := isIso_μ_Qh_of_kFlat ((quotient _ _).obj K₁)
    (((Etale.etaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
      ((quotient _ _).obj T₁)) hK₁
  have := isIso_μ_Qh_of_kFlat (((f)^*[A].mapHomotopyCategory (.up ℤ)).obj
    ((quotient _ _).obj K₁)) ((quotient _ _).obj T₁) hK₁'
  rw [← IsIso.eq_comp_inv] at h
  rw [h]
  infer_instance

omit [HasSmallSiteSheafify A] in
/-- **Derived projection formula for an étale morphism** `u : U ⟶ X`: the projection map
`D(u_!)(Lu^*K ⊗ᴸ T) ⟶ K ⊗ᴸ D(u_!)T` of the adjunction `D(u_!) ⊣ Lu^*`, for the monoidal
structure `leftDerivedUpperStarMonoidal` of `Lu^*`, is an isomorphism. -/
theorem isIso_projectionMap_derivedEtaleLowerShriek {U : Scheme.{u}} (f : U ⟶ X) [Etale f]
    [(f)^*[A].PreservesFlat]
    [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]
    [(U.smallEtaleTopology.W (A := A)).IsMonoidal] [(X.smallEtaleTopology.W (A := A)).IsMonoidal]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarMonoidal A f
    IsIso (Functor.Monoidal.projectionMap
      (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction (A := A) f) K) := by
  let := leftDerivedUpperStarMonoidal A f
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution
    (Sheaf X.smallEtaleTopology A)).some.reduced
  have hι := (ObjectProperty.flat (A := Sheaf X.smallEtaleTopology A)).essImage_ι_le
  let K₀ := _root_.DerivedCategory.Q.objPreimage K
  let K₁ := Λ.resolutionFunctor.obj K₀
  have : IsIso (_root_.DerivedCategory.Q.map (Λ.resolutionNatTrans.app K₀)) :=
    (_root_.DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  let eK : K ≅ _root_.DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K₁) :=
    (_root_.DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (asIso (_root_.DerivedCategory.Q.map (Λ.resolutionNatTrans.app K₀))).symm ≪≫
      (_root_.DerivedCategory.quotientCompQhIso _).symm.app K₁
  have hK₁ := (HomotopyCategory.kFlat_quotient_obj_iff _).2 (Λ.kFlat_resolutionFunctor_obj hι K₀)
  have hK₁' := kFlatUpperStar_quotient_obj_resolutionFunctor_obj A f Λ K₀
  have : ∀ G, IsIso (Functor.Monoidal.projectionMap
      (Etale.etaleLowerShriekUpperStarAdjunction A f inferInstance) G) :=
    fun G ↦ Etale.isIso_projectionMap_etaleLowerShriek A inferInstance G
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  let T₀ := _root_.DerivedCategory.Q.objPreimage T
  let eT : T ≅ _root_.DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj T₀) :=
    (_root_.DerivedCategory.Q.objObjPreimageIso T).symm ≪≫
      (_root_.DerivedCategory.quotientCompQhIso _).symm.app T₀
  have : PreservesColimitsOfSize.{0, 0} (Etale.etaleLowerShriek A f inferInstance) :=
    (Etale.etaleLowerShriekUpperStarAdjunction A f inferInstance).leftAdjoint_preservesColimits
  have := Functor.Monoidal.isIso_projectionMap_mapHomologicalComplex (f)^*[A]
    (Etale.etaleLowerShriekUpperStarAdjunction A f inferInstance) K₁
  have := isIso_projectionMap_derivedEtaleLowerShriek_app_Qh (A := A) f K₁ hK₁ hK₁' T₀
  have := Functor.Monoidal.isIso_projectionMap_app_of_iso
    (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction (A := A) f) eK
    (_root_.DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj T₀))
  have hn := (Functor.Monoidal.projectionMap
    (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction (A := A) f) K).naturality eT.hom
  have : IsIso ((Functor.Monoidal.projectionMap
      (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction (A := A) f) K).app T ≫
      K ◁ (Etale.etaleLowerShriek A f inferInstance).mapDerivedCategory.map eT.hom) := by
    erw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (K ◁ (Etale.etaleLowerShriek A f inferInstance).mapDerivedCategory.map eT.hom)

omit [HasSmallSiteSheafify A] in
/-- For étale `u` and `K` with `Lu^*K` dualizable, `Lu^*` sends the comparison
`RHom(K, 𝟙) ⊗ᴸ K ⟶ RHom(K, K)` to an isomorphism. By
`CategoryTheory.Functor.Monoidal.isIso_map_ihomUnitTensorToIhom`, this follows from the derived
projection formula `isIso_projectionMap_derivedEtaleLowerShriek`. -/
theorem isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhomEtale_of_isDualizableEtale_general
    {U : Scheme.{u}} (f : U ⟶ X) [Etale f] [(f)^*[A].PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hK : DerivedCategory.IsDualizableEtale ((L((f)^*[A])).obj K)) :
    IsIso ((L((f)^*[A])).map (DerivedCategory.ihomUnitTensorToIhomEtale K)) := by
  let := leftDerivedUpperStarMonoidal A f
  have := isIso_projectionMap_derivedEtaleLowerShriek (A := A) f K
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := Etale.DerivedCategory.nonempty_exactPairing_swap ((L((f)^*[A])).obj K)
    ((L((f)^*[A])).obj K)ᘁ
  have := MonoidalClosed.isIso_ihomUnitTensorToIhom ((L((f)^*[A])).obj K)ᘁ ((L((f)^*[A])).obj K)
    ((L((f)^*[A])).obj K)
  exact Functor.Monoidal.isIso_map_ihomUnitTensorToIhom
    (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction (A := A) f) K K

end Projection

/-- For an étale morphism `u : U ⟶ X` and `K` whose derived pullback `Lu^*K` is dualizable, the
derived pullback of the comparison `RHom(K, Λ_X) ⊗ᴸ K ⟶ RHom(K, K)` is an isomorphism: for
étale `u` the derived pullback commutes with the internal hom, and the comparison for the
dualizable `Lu^*K` is an isomorphism. -/
theorem isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhomEtale_of_isDualizableEtale
    {U : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : DerivedCategory.IsDualizableEtale ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    IsIso ((L((f)^*[ModuleCat.{u + 1} Λ])).map (DerivedCategory.ihomUnitTensorToIhomEtale K)) :=
  isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhomEtale_of_isDualizableEtale_general f K _hK

/-- On a member `u : U ⟶ X` of an étale cover on which `K` is isomorphic to a bounded complex of
finite projective `Λ_U`-modules, the derived pullback of the comparison
`RHom(K, Λ_X) ⊗ᴸ K ⟶ RHom(K, K)` is an isomorphism. -/
theorem isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhom_of_trivialization
    {U : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hP : ∀ n, ∃ m : ℕ, Nonempty (Retract (P.X n)
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Fin m → Λ)))))
    (e : (L((f)^*[ModuleCat.{u + 1} Λ])).obj K ≅ DerivedCategory.Q.obj P) :
    IsIso ((L((f)^*[ModuleCat.{u + 1} Λ])).map (DerivedCategory.ihomUnitTensorToIhomEtale K)) :=
  isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhomEtale_of_isDualizableEtale f K
    (isDualizableEtale_of_trivialization P a b ha hb hP e)

/-- A complex which is perfect on the coefficient site is dualizable for the derived tensor
product: dualizability can be checked on an étale cover
(`AlgebraicGeometry.Etale.DerivedCategory.isDualizable_of_cover`), and on the members of a
trivializing cover the comparison map is an isomorphism
(`isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhom_of_trivialization`). -/
theorem DerivedCategory.IsSitePerfect.isDualizable
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.IsSitePerfect K) : DerivedCategory.IsDualizableEtale K := by
  obtain ⟨𝒰, h⟩ := hK
  refine DerivedCategory.isDualizable_of_cover K 𝒰 fun i ↦ ?_
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := h i
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  exact isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhom_of_trivialization (𝒰.f i) K P a b
    ha hb hP e

/-- Blueprint `proposition-six-operations-change-coefficients`: Basic operations and coefficient
reduction; the internal hom between finite levels.

If the first variable `K` is perfect on the coefficient site, the internal hom commutes with
the reduction of the coefficients along `Λ ⟶ Λ/J`, for any ideal `J`:
`RHom(K, L) ⊗ᴸ (Λ/J)_X ≅ RHom(K, L ⊗ᴸ (Λ/J)_X)`. As in the blueprint, `K` being site-perfect,
its internal hom is a tensor product with its coefficient dual, which commutes with coefficient
change. -/
theorem nonempty_iso_reductionModIdeal_derivedHom_of_isSitePerfect (J : Ideal Λ)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.IsSitePerfect K)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((reductionModIdeal Λ X J).obj
        ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj L) ≅
      (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj ((reductionModIdeal Λ X J).obj L)) := by
  obtain ⟨e⟩ := DerivedCategory.nonempty_iso_derivedHom_derivedTensor_of_isDualizable
    hK.isDualizable L ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Λ ⧸ J))))
  exact ⟨e.symm⟩

end Etale

end AlgebraicGeometry
