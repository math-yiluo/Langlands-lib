/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.FieldTheory.SeparableClosure
public import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField
public import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits

/-!
# The geometric generic point in the pro-étale site

Let `X` be an integral scheme with function field `K` and let `Kˢᵉᵖ = SeparableClosure K`. The
composite `Spec Kˢᵉᵖ ⟶ Spec K ⟶ X` is weakly étale: `Spec K ⟶ X` is the spectrum of a
localization of the ring of an affine open (ind-Zariski, hence weakly étale), and `K → Kˢᵉᵖ` is
a separable algebraic extension, hence ind-étale. This gives an object
`AlgebraicGeometry.Scheme.ProEt.genericPointSep X` of `X_proét`, on which the Galois group
`Gal(Kˢᵉᵖ/K)` acts (on the right).

A nonempty weakly étale scheme over a separably closed field has a section
(`AlgebraicGeometry.exists_comp_eq_id_of_weaklyEtale_of_isSepClosed`), so every covering
sieve of an object of `X_proét` whose underlying scheme is the spectrum of a separably closed
field contains the identity. For such an object `T`, taking sections over `T` preserves
epimorphisms of sheaves with values in a concrete category, and evaluating the map from a
presheaf to its sheafification at `T` is bijective.

## Main definitions

- `AlgebraicGeometry.Scheme.ProEt.genericPointSep`: the object `Spec Kˢᵉᵖ ⟶ X` of `X_proét`.
- `AlgebraicGeometry.Scheme.ProEt.genericPointSepAut`: the action of `Gal(Kˢᵉᵖ/K)` on it.

## Main statements

- `Algebra.IndEtale.of_isSeparable`: a separable algebraic field extension is ind-étale.
- `AlgebraicGeometry.Scheme.weaklyEtale_fromSpecStalk`: `Spec 𝒪_{X,x} ⟶ X` is weakly étale.
- `AlgebraicGeometry.Scheme.ProEt.id_mem_of_mem_topology_of_isSepClosed`: covering sieves of an
  object whose underlying scheme is the spectrum of a separably closed field contain `𝟙`.
- `AlgebraicGeometry.Scheme.ProEt.genericPointSepAut_mul`:
  `genericPointSepAut X (σ * τ) = genericPointSepAut X σ ≫ genericPointSepAut X τ`.
- `AlgebraicGeometry.ProEtale.preservesEpimorphisms_sheafSections_of_forall_id_mem`,
  `AlgebraicGeometry.ProEtale.bijective_toSheafify_app_of_forall_id_mem`, and their
  specialisations to `genericPointSep`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

/-- A separable algebraic field extension `L / K` is ind-étale: every finitely generated
`K`-subalgebra of `L` is a finite separable field extension of `K`, hence étale. -/
theorem Algebra.IndEtale.of_isSeparable (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] : Algebra.IndEtale K L :=
  .of_forall_fg_etale fun A hA ↦ by
    let := (Subalgebra.isField_of_algebraic A).toField
    have : Algebra.IsSeparable K A := .of_algHom K L A.val
    have : Algebra.FiniteType K A := hA.finiteType
    have : Algebra.FormallyEtale K A := .of_isSeparable K A
    exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

namespace AlgebraicGeometry

/-- The canonical morphism `Spec 𝒪_{X,x} ⟶ X` is weakly étale: on an affine open neighbourhood
`U` of `x`, it is the spectrum of the localization `Γ(X, U) → 𝒪_{X,x}`, which is ind-Zariski. -/
instance Scheme.weaklyEtale_fromSpecStalk (X : Scheme.{u}) (x : X) :
    WeaklyEtale (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk]
  let := (X.presheaf.germ U x hxU).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.IndZariski Γ(X, U) (X.presheaf.stalk x) :=
    .of_isLocalization _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have : WeaklyEtale (Spec.map (X.presheaf.germ U x hxU)) :=
    weaklyEtale_SpecMap_algebraMap (R := Γ(X, U)) (S := X.presheaf.stalk x)
  infer_instance

namespace Scheme.ProEt

variable {X : Scheme.{u}}

/-- Let `T` be an object of `X_proét` whose underlying scheme is isomorphic to the spectrum of
a separably closed field `L`. Every covering sieve of `T` contains the identity: a member
`f : V ⟶ T` of a pro-étale covering family with `V` nonempty has a section. -/
lemma id_mem_of_mem_topology_of_isSepClosed {L : Type u} [Field L] [IsSepClosed L]
    {T : X.ProEt} (e : T.left ≅ Spec (.of L)) {S : Sieve T} (hS : S ∈ topology X T) :
    S (𝟙 T) := by
  obtain ⟨R, hR, hRS⟩ := mem_topology_iff.1 hS
  have hR' : R.map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
      Scheme.precoverage @WeaklyEtale T.left :=
    Scheme.propQCPrecoverage_le_precoverage _ hR
  obtain ⟨Y, g, hg, x, -⟩ := hR'.1 (e.inv.base (IsLocalRing.closedPoint L))
  obtain ⟨hg⟩ := hg
  obtain @⟨V, f, hf⟩ := hg
  have : WeaklyEtale f.left := by
    have : WeaklyEtale (f.left ≫ T.hom) := by
      rw [MorphismProperty.Over.w]
      infer_instance
    exact WeaklyEtale.of_comp f.left T.hom
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale_of_isSepClosed (f.left ≫ e.hom) x
  have hσ' : σ ≫ f.left = e.inv := by
    rw [← cancel_mono e.hom, Category.assoc, hσ, e.inv_hom_id]
  have hσ'' : (e.hom ≫ σ) ≫ V.hom = T.hom := by
    rw [← MorphismProperty.Over.w f, Category.assoc, reassoc_of% hσ', e.hom_inv_id_assoc]
  have : S (MorphismProperty.Over.homMk (A := T) (e.hom ≫ σ) hσ'' ≫ f) :=
    S.downward_closed (hRS _ _ hf) _
  convert this
  refine MorphismProperty.Over.Hom.ext ?_
  exact (by rw [Category.assoc, hσ', e.hom_inv_id] : (e.hom ≫ σ) ≫ f.left = 𝟙 T.left).symm

end Scheme.ProEt

namespace ProEtale

variable {X : Scheme.{u}}

section Concrete

variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A]

/-- Let `T` be an object of `X_proét` all of whose covering sieves contain the identity. An
epimorphism of pro-étale sheaves with values in a concrete category `A` is surjective on
sections over `T`. -/
lemma surjective_app_of_epi_of_forall_id_mem {T : X.ProEt}
    (hT : ∀ S : Sieve T, S ∈ Scheme.ProEt.topology X T → S (𝟙 T))
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective A]
    [HasSheafify (Scheme.ProEt.topology X) A]
    [(Scheme.ProEt.topology X).HasSheafCompose (CategoryTheory.forget A)]
    [Balanced (Sheaf (Scheme.ProEt.topology X) A)]
    {F G : Sheaf (Scheme.ProEt.topology X) A} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op T)) := by
  have := (Sheaf.isLocallySurjective_iff_epi' A φ).2 inferInstance
  intro s
  obtain ⟨t, ht⟩ := hT _ (Presheaf.imageSieve_mem (Scheme.ProEt.topology _) φ.hom s)
  exact ⟨t, by simpa using ht⟩

/-- Let `T` be an object of `X_proét` all of whose covering sieves contain the identity. Taking
sections over `T` preserves epimorphisms of pro-étale sheaves with values in a concrete
category. -/
lemma preservesEpimorphisms_sheafSections_of_forall_id_mem {T : X.ProEt}
    (hT : ∀ S : Sieve T, S ∈ Scheme.ProEt.topology X T → S (𝟙 T))
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective A]
    [HasSheafify (Scheme.ProEt.topology X) A]
    [(Scheme.ProEt.topology X).HasSheafCompose (CategoryTheory.forget A)]
    [Balanced (Sheaf (Scheme.ProEt.topology X) A)] :
    ((sheafSections (Scheme.ProEt.topology X) A).obj (op T)).PreservesEpimorphisms where
  preserves φ _ := (CategoryTheory.forget A).epi_of_epi_map
    ((epi_iff_surjective _).2 (surjective_app_of_epi_of_forall_id_mem hT φ))

end Concrete

section Sheafify

variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [HasSheafify (Scheme.ProEt.topology X) A]
  [(Scheme.ProEt.topology X).HasSheafCompose (CategoryTheory.forget A)]
  [(Scheme.ProEt.topology X).PreservesSheafification (CategoryTheory.forget A)]

/-- Let `T` be an object of `X_proét` all of whose covering sieves contain the identity. The map
from a presheaf with values in a concrete category to its pro-étale sheafification is bijective
on sections over `T`. -/
lemma bijective_toSheafify_app_of_forall_id_mem {T : X.ProEt}
    (hT : ∀ S : Sieve T, S ∈ Scheme.ProEt.topology X T → S (𝟙 T)) (G : X.ProEtᵒᵖ ⥤ A) :
    Function.Bijective ((toSheafify (Scheme.ProEt.topology X) G).app (op T)) := by
  refine ⟨fun x y hxy ↦ ?_, fun s ↦ ?_⟩
  · simpa using hT _
      (Presheaf.equalizerSieve_mem (Scheme.ProEt.topology X) (toSheafify _ G) x y hxy)
  · obtain ⟨t, ht⟩ := hT _
      (Presheaf.imageSieve_mem (Scheme.ProEt.topology X) (toSheafify _ G) s)
    exact ⟨t, by simpa using ht⟩

end Sheafify

end ProEtale

namespace Scheme.ProEt

variable (X : Scheme.{u}) [IsIntegral X]

/-- The geometric generic point `Spec Kˢᵉᵖ ⟶ Spec K ⟶ X` of an integral scheme `X` with function
field `K`, where `Kˢᵉᵖ = SeparableClosure K`. -/
noncomputable def genericPointSepHom :
    Spec (.of (SeparableClosure X.functionField)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap X.functionField (SeparableClosure X.functionField))) ≫
    X.fromSpecStalk (genericPoint X)

instance : WeaklyEtale (genericPointSepHom X) := by
  have := Algebra.IndEtale.of_isSeparable X.functionField (SeparableClosure X.functionField)
  rw [genericPointSepHom]
  infer_instance

/-- The geometric generic point `Spec Kˢᵉᵖ ⟶ X` of an integral scheme `X`, as an object of the
small pro-étale site of `X`. -/
noncomputable def genericPointSep : X.ProEt :=
  Scheme.ProEt.mk (genericPointSepHom X)

/-- The underlying scheme of the geometric generic point is `Spec Kˢᵉᵖ`. -/
lemma genericPointSep_left :
    (genericPointSep X).left = Spec (.of (SeparableClosure X.functionField)) :=
  rfl

/-- The structure morphism of the geometric generic point. -/
lemma genericPointSep_hom : (genericPointSep X).hom = genericPointSepHom X :=
  rfl

/-- The action of `σ ∈ Gal(Kˢᵉᵖ/K)` on the geometric generic point: the automorphism
`Spec σ` of `Spec Kˢᵉᵖ` over `X`. -/
noncomputable def genericPointSepAut
    (σ : SeparableClosure X.functionField ≃ₐ[X.functionField] SeparableClosure X.functionField) :
    genericPointSep X ⟶ genericPointSep X :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
    rw [genericPointSep_hom, genericPointSepHom, ← Category.assoc, ← Spec.map_comp]
    congr 3
    ext x
    simp)

lemma genericPointSepAut_left
    (σ : SeparableClosure X.functionField ≃ₐ[X.functionField] SeparableClosure X.functionField) :
    (genericPointSepAut X σ).left = Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  rfl

@[simp]
lemma genericPointSepAut_one : genericPointSepAut X 1 = 𝟙 _ := by
  refine MorphismProperty.Over.Hom.ext ?_
  rw [genericPointSepAut_left]
  exact Spec.map_id _

/-- The Galois action on the geometric generic point is a right action:
`Spec (σ * τ) = Spec σ ≫ Spec τ`. -/
lemma genericPointSepAut_mul
    (σ τ : SeparableClosure X.functionField ≃ₐ[X.functionField]
      SeparableClosure X.functionField) :
    genericPointSepAut X (σ * τ) = genericPointSepAut X σ ≫ genericPointSepAut X τ := by
  refine MorphismProperty.Over.Hom.ext ?_
  rw [MorphismProperty.Comma.comp_left, genericPointSepAut_left, genericPointSepAut_left,
    genericPointSepAut_left, ← Spec.map_comp]
  rfl

/-- Every covering sieve of the geometric generic point contains the identity. -/
lemma id_mem_genericPointSep {S : Sieve (genericPointSep X)}
    (hS : S ∈ topology X (genericPointSep X)) : S (𝟙 _) :=
  id_mem_of_mem_topology_of_isSepClosed (Iso.refl _) hS

end Scheme.ProEt

namespace ProEtale

variable (X : Scheme.{u}) [IsIntegral X]

/-- Taking sections over the geometric generic point preserves epimorphisms of pro-étale sheaves
with values in a concrete category. -/
lemma preservesEpimorphisms_sheafSections_genericPointSep
    {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A]
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective A]
    [HasSheafify (Scheme.ProEt.topology X) A]
    [(Scheme.ProEt.topology X).HasSheafCompose (CategoryTheory.forget A)]
    [Balanced (Sheaf (Scheme.ProEt.topology X) A)] :
    ((sheafSections (Scheme.ProEt.topology X) A).obj
      (op (Scheme.ProEt.genericPointSep X))).PreservesEpimorphisms :=
  preservesEpimorphisms_sheafSections_of_forall_id_mem
    fun _ ↦ Scheme.ProEt.id_mem_genericPointSep X

/-- The map from a presheaf with values in a concrete category to its pro-étale sheafification is
bijective on sections over the geometric generic point. -/
lemma bijective_toSheafify_app_genericPointSep
    {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type (u + 1)}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [HasSheafify (Scheme.ProEt.topology X) A]
    [(Scheme.ProEt.topology X).HasSheafCompose (CategoryTheory.forget A)]
    [(Scheme.ProEt.topology X).PreservesSheafification (CategoryTheory.forget A)]
    (G : X.ProEtᵒᵖ ⥤ A) :
    Function.Bijective ((toSheafify (Scheme.ProEt.topology X) G).app
      (op (Scheme.ProEt.genericPointSep X))) :=
  bijective_toSheafify_app_of_forall_id_mem (fun _ ↦ Scheme.ProEt.id_mem_genericPointSep X) G

end ProEtale

end AlgebraicGeometry
