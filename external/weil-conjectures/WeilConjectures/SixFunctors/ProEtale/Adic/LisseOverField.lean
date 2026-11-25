/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
public import WeilConjectures.SixFunctors.ProEtale.Adic.IrreducibleLisse
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseLattice
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseLocallyFree
public import WeilConjectures.SixFunctors.ProEtale.GenericPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar

/-!
# Constructible module objects on the spectrum of a field are lisse

Let `K` be a field and `Λ` a commutative condensed ring. A constructible module object over
`Λ_{Spec K}` is pro-étale locally finitely presented: the stratum through the point of `Spec K`
is an immersion with nonempty source into `Spec K`, hence an isomorphism
(`ProEtale.CondensedRing.IsConstructibleModuleObject.isLocallyFinitelyPresented_of_isField`).
If `K` is algebraically closed, every pro-étale cover of `Spec K` has a section, so such a module
object is even finitely presented
(`ProEtale.CondensedRing.IsLocallyFinitelyPresented.isFinitelyPresented_of_isAlgClosed`).

For `Λ = ℚ̲̄_ℓ`, through the equivalence `AdicSheaf ℓ X ≌ Mod_{ℚ̲̄_ℓ,X}`, a finitely presented
module object on an irreducible scheme is a lisse `ℓ`-adic sheaf, the cokernel of a morphism of
lisse sheaves on an irreducible scheme being lisse
(`AlgebraicGeometry.ProEtale.isAdicLisseSheaf_of_isFinitelyPresented`). Pulling back to an
algebraic closure, the `ℓ`-adic sheaf of a constructible module object over `ℚ̲̄_ℓ` on the spectrum
of a perfect field is lisse
(`AlgebraicGeometry.ProEtale.isAdicLisseSheaf_inverse_obj_of_isConstructibleModuleObject`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable {Λ} in
/-- A constructible module object on the spectrum of a field is pro-étale locally finitely
presented: the stratum through the point is an immersion with nonempty source into the point,
hence an isomorphism. -/
theorem IsConstructibleModuleObject.isLocallyFinitelyPresented_of_isField {K : Type u} [Field K]
    {M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of K)))}
    (hM : IsConstructibleModuleObject (condensedRingObj Λ (Spec (.of K))) M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ (Spec (.of K))) M := by
  obtain ⟨S, hS⟩ := hM
  have hx : IsLocalRing.closedPoint K ∈ ⋃ a, S.stratum a := by
    rw [S.iUnion_stratum_eq_univ]
    trivial
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx
  rw [← S.range_immersion a] at ha
  obtain ⟨z, -⟩ := ha
  have : Nonempty (S.domain a) := ⟨z⟩
  have : IsIso (S.immersion a) := IsImmersion.isIso_of_nonempty _
  exact (IsLocallyFinitelyPresented.upperStar Λ (inv (S.immersion a))
    ((isLocallyFinitelyPresented_mapMod_iff Λ _ _).1 (hS a))).of_iso
    (((upperStarComp Λ _ _).app M).symm ≪≫ (upperStarCongr Λ (IsIso.inv_hom_id _)).app M ≪≫
      (upperStarId Λ _).app M)

variable {Λ} in
/-- A pro-étale locally finitely presented module object on the spectrum of an algebraically
closed field is finitely presented: a member `f : V ⟶ Spec K` of the cover with `V` nonempty has
a section `σ`, and `M ≅ σ^* f^* M`. -/
theorem IsLocallyFinitelyPresented.isFinitelyPresented_of_isAlgClosed {K : Type u} [Field K]
    [IsAlgClosed K]
    {M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of K)))}
    (hM : IsLocallyFinitelyPresented (condensedRingObj Λ (Spec (.of K))) M) :
    Mod.IsFinitelyPresented (condensedRingObj Λ (Spec (.of K))) M := by
  obtain ⟨𝒰, h𝒰⟩ := (isLocallyFinitelyPresented_iff M).1 hM
  have hR' : _ ∈ Scheme.precoverage (@WeaklyEtale : MorphismProperty Scheme.{u}) _ :=
    (show Scheme.proetalePrecoverage ≤ Scheme.precoverage @WeaklyEtale from inf_le_right) _
      𝒰.mem₀
  rw [Scheme.ofArrows_mem_precoverage_iff (@WeaklyEtale : MorphismProperty Scheme.{u})] at hR'
  obtain ⟨i, v, -⟩ := hR'.1 (IsLocalRing.closedPoint K)
  have : WeaklyEtale (𝒰.f i) := hR'.2 i
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale (𝒰.f i) v
  exact (IsFinitelyPresented.upperStar Λ σ (h𝒰 i)).of_iso
    (((upperStarComp Λ _ _).app M).symm ≪≫ (upperStarCongr Λ hσ).app M ≪≫
      (upperStarId Λ _).app M)

end CondensedRing

variable {l : ℕ} [Fact l.Prime]

/-- The `ℓ`-adic sheaf of a free module object of finite rank over `ℚ̲̄_ℓ,X` is lisse: it is a
finite direct sum of copies of `ℚ̄_ℓ,X`. -/
theorem isAdicLisseSheaf_inverse_obj_finiteFree (X : Scheme.{u}) (n : ℕ) :
    IsAdicLisseSheaf ((adicSheafEquivCondensedMod l X).inverse.obj
      (Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) X) n)) :=
  ((isAdicLisseSheaf_adicConstantSheaf X).biproduct_const n).of_iso
    ((biproduct.mapIso fun _ ↦ (adicSheafEquivCondensedMod l X).unitIso.app _ ≪≫
        (adicSheafEquivCondensedMod l X).inverse.mapIso
          (adicSheafEquivCondensedModUnitIso l X)) ≪≫
      ((adicSheafEquivCondensedMod l X).inverse.mapBiproduct _).symm)

/-- **A finitely presented module object on an irreducible scheme is lisse**: if the module
object over `ℚ̲̄_ℓ,Y` of an `ℓ`-adic sheaf `F` is the cokernel of a morphism of free module
objects of finite rank, then `F` is the cokernel of a morphism of lisse sheaves, hence lisse. -/
theorem isAdicLisseSheaf_of_isFinitelyPresented {Y : Scheme.{u}} [IrreducibleSpace Y]
    {F : AdicSheaf l Y}
    (hF : Mod.IsFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) Y)
      ((adicSheafEquivCondensedMod l Y).functor.obj F)) :
    IsAdicLisseSheaf F := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := hF
  exact (IsAdicLisseSheaf.kernel_cokernel_of_irreducibleSpace
    (isAdicLisseSheaf_inverse_obj_finiteFree Y m) (isAdicLisseSheaf_inverse_obj_finiteFree Y n)
      ((adicSheafEquivCondensedMod l Y).inverse.map f)).2.of_iso
    ((PreservesCokernel.iso _ f).symm ≪≫ (adicSheafEquivCondensedMod l Y).inverse.mapIso e.symm ≪≫
      ((adicSheafEquivCondensedMod l Y).unitIso.app F).symm)

/-- The `ℓ`-adic sheaf of a constructible module object over `ℚ̲̄_ℓ` on the spectrum of a field
`K` is lisse, provided `Spec K` has a weakly étale, surjective, quasi-compact cover by the
spectrum of an algebraically closed field `Ω`: the pullback to `Spec Ω` is constructible, hence
finitely presented, hence lisse, `Spec Ω` being irreducible. -/
theorem isAdicLisseSheaf_inverse_obj_of_isConstructibleModuleObject_of_cover {K Ω : Type u}
    [Field K] [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of K)) [WeaklyEtale g]
    [Surjective g] [QuasiCompact g]
    {M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) (Spec (.of K)))}
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) (Spec (.of K))) M) :
    IsAdicLisseSheaf ((adicSheafEquivCondensedMod l (Spec (.of K))).inverse.obj M) := by
  have hg : IsAdicLisseSheaf ((g)^*ᵃ[l].obj
      ((adicSheafEquivCondensedMod l (Spec (.of K))).inverse.obj M)) :=
    isAdicLisseSheaf_of_isFinitelyPresented
      ((CondensedRing.IsLocallyFinitelyPresented.isFinitelyPresented_of_isAlgClosed
        (CondensedRing.IsConstructibleModuleObject.isLocallyFinitelyPresented_of_isField
          (CondensedRing.IsConstructibleModuleObject.upperStar _ g hM))).of_iso
        (((CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} l) g).mapIso
          ((adicSheafEquivCondensedMod l (Spec (.of K))).counitIso.app M)).symm ≪≫
          ((adicUpperStarCompCondensedModIso l g).app _).symm))
  obtain ⟨n, ⟨e⟩⟩ := hg.exists_iso_biproduct_of_isAlgClosed
  exact IsAdicLisseSheaf.of_upperStar_iso g e

/-- **Constructible module objects on the spectrum of a perfect field are lisse**: the `ℓ`-adic
sheaf of a constructible module object over `ℚ̲̄_ℓ` on `Spec K` is lisse, trivialised on the
pro-étale cover `Spec K̄ ⟶ Spec K`. -/
theorem isAdicLisseSheaf_inverse_obj_of_isConstructibleModuleObject {K : Type u} [Field K]
    [PerfectField K]
    {M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) (Spec (.of K)))}
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) (Spec (.of K))) M) :
    IsAdicLisseSheaf ((adicSheafEquivCondensedMod l (Spec (.of K))).inverse.obj M) := by
  have : Algebra.IndEtale K (AlgebraicClosure K) :=
    Algebra.IndEtale.of_isSeparable K (AlgebraicClosure K)
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) :=
    ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  exact isAdicLisseSheaf_inverse_obj_of_isConstructibleModuleObject_of_cover
    (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) hM

end AlgebraicGeometry.ProEtale
