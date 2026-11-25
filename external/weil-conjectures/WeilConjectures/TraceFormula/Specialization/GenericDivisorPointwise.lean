/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericDivisorLocal

/-!

# Generic vanishing of the defect is checked at the generic points of the centre

Let `X` be a separated `k`-scheme of finite type and `Z = V(I) ⊆ X` a closed subscheme. The defect
`C_{X,Z}(L)` *vanishes near* a point `z ∈ Z` if its restriction to the inverse image in
`N_⊥ Z ≅ Z ⊗ k'` of an open neighbourhood of `z` in `Z` is zero
(`ProEtale.CondensedRing.defectVanishesNear`). This file shows:

* the defect vanishes generically on `Z` as soon as it vanishes near every generic point of an
  irreducible component of `Z`
  (`ProEtale.CondensedRing.genericallyVanishingDefect_of_forall_defectVanishesNear`): the union of
  the neighbourhoods contains every generic point, hence is dense;
* vanishing near a point can be checked on an open neighbourhood `V` of that point in `X`
  (`ProEtale.CondensedRing.defectVanishesNear_of_isOpenImmersion`), by the smooth exchange.

Together, they reduce blueprint `lemma-vanishing-generic-points-principal-divisor--1` to the
vanishing of the defect near each generic point `ζ` of `Z`, on an arbitrarily small open
neighbourhood of `ζ` in `X`
(`ProEtale.CondensedRing.exists_dense_isZero_specializationDefect_of_forall_isOpenImmersion`).

-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace ZeroObject

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Vanishing on a finite union of opens -/

section Union

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- A complex on a scheme `S` whose derived pullbacks along a finite quasi-compact jointly
surjective family vanish is zero. -/
lemma isZero_of_forall_isZero_leftDerivedUpperStar {S : Scheme.{u}} {κ : Type*} [Finite κ]
    {S' : κ → Scheme.{u}} (g : ∀ a, S' a ⟶ S) [∀ a, QuasiCompact (g a)]
    (hg : ∀ x, ∃ a, x ∈ Set.range (g a).base)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S))} (h : ∀ a, IsZero (L((g a)^*⟦Λ⟧).obj B)) : IsZero B := by
  have (a : κ) : IsIso ((L((g a)^*⟦Λ⟧)).map (0 : B ⟶ 0)) :=
    (h a).isIso (Functor.map_isZero _ (isZero_zero _)) _
  exact ((isIsoZero_iff_source_target_isZero _ _).1
    ((jointlyReflectIsomorphisms_leftDerivedUpperStar_of_cover Λ g hg).isIso (0 : B ⟶ 0))).1

/-- On a noetherian scheme `T`, a complex whose restrictions to finitely many opens `W_a` covering
an open `W₀` vanish has vanishing restriction to `W₀`. -/
lemma isZero_leftDerivedUpperStar_ι_obj_of_cover {T : Scheme.{u}} [NoetherianSpace T]
    {κ : Type*} [Finite κ] (W₀ : T.Opens) (W : κ → T.Opens) (hW : ∀ a, W a ≤ W₀)
    (hcov : ∀ x ∈ W₀, ∃ a, x ∈ W a)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))} (h : ∀ a, IsZero (L(((W a).ι)^*⟦Λ⟧).obj A)) :
    IsZero (L((W₀.ι)^*⟦Λ⟧).obj A) := by
  have (a : κ) : NoetherianSpace (W a).toScheme := inferInstanceAs (NoetherianSpace (W a : Set T))
  refine isZero_of_forall_isZero_leftDerivedUpperStar Λ (fun a ↦ T.homOfLE (hW a)) (fun x ↦ ?_)
    fun a ↦ ?_
  · obtain ⟨a, ha⟩ := hcov x.1 x.2
    exact ⟨a, ⟨⟨x.1, ha⟩, Subtype.ext (by simp)⟩⟩
  · exact (isZero_leftDerivedUpperStar_obj_of_eq Λ (T.homOfLE_ι (hW a)).symm (h a)).of_iso
      ((leftDerivedUpperStarComp Λ (T.homOfLE (hW a)) W₀.ι).app A).symm

end Union

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The defect `C_{X,Z}(L)` *vanishes near* the point `z` of the centre: its restriction to the
inverse image in `N_⊥ Z ≅ Z ⊗ k'` of some open neighbourhood of `z` in `Z` is zero. -/
def defectVanishesNear
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) (z : (centre X I).left) : Prop :=
  ∃ U : (centre X I).left.Opens, z ∈ U ∧
    IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦Λ⟧)).obj
      (specializationDefect X I k' Λ L))

/-- **Generic vanishing at the generic points**: if the defect `C_{X,Z}(L)` vanishes near every
generic point of an irreducible component of `Z`, it vanishes generically on `Z`. -/
theorem genericallyVanishingDefect_of_forall_defectVanishesNear
    [NoetherianSpace (centre X I).left]
    [NoetherianSpace (deformationSpecialFibre (centre X I) ⊥ k').left]
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (h : ∀ z : (centre X I).left, closure {z} ∈ irreducibleComponents (centre X I).left →
      defectVanishesNear X I k' Λ L z) :
    genericallyVanishingDefect X I k' Λ L := by
  have := (NoetherianSpace.finite_irreducibleComponents (α := (centre X I).left)).to_subtype
  have hz (C : irreducibleComponents (centre X I).left) :
      closure {C.2.1.genericPoint} = C.1 := by
    have hC := C.2.1.isGenericPoint_genericPoint_closure
    rwa [(isClosed_of_mem_irreducibleComponents _ C.2).closure_eq] at hC
  choose U hU hUz using fun C : irreducibleComponents (centre X I).left ↦
    h C.2.1.genericPoint ((hz C).symm ▸ C.2)
  refine ⟨⨆ C, U C, ?_, ?_⟩
  · refine dense_iff_inter_open.2 fun O hO ⟨x, hx⟩ ↦ ?_
    let C : irreducibleComponents (centre X I).left :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    have hxC : x ∈ closure {C.2.1.genericPoint} := (hz C).symm ▸ mem_irreducibleComponent
    refine ⟨C.2.1.genericPoint, (specializes_iff_mem_closure.2 hxC).mem_open hO hx, ?_⟩
    exact (Opens.mem_iSup (s := U)).2 ⟨C, hU C⟩
  · exact isZero_leftDerivedUpperStar_ι_obj_of_cover Λ _ _
      (fun C ↦ Hom.preimage_mono _ (le_iSup U C)) (fun x hx ↦ (Opens.mem_iSup (s := U)).1 hx) hUz

/-! ### Reduction to a neighbourhood of a generic point -/

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

variable {X} in
/-- **Vanishing near a point is local on `X`**: let `g : V ⟶ X` be an open immersion and `z'` a
point of `Z ∩ V`. If the defect `C_{V, Z ∩ V}(g^* L)` vanishes near `z'`, then `C_{X,Z}(L)`
vanishes near the image of `z'` in `Z`. -/
theorem defectVanishesNear_of_isOpenImmersion {V : Over (Spec (.of k))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom] (g : V ⟶ X)
    [IsOpenImmersion g.left] (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (z' : (centre V (I.comap g.left)).left)
    (h : defectVanishesNear V (I.comap g.left) k' (Profinite.padicAlgClRingObj ℓ)
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj L).obj z') :
    defectVanishesNear X I k' (Profinite.padicAlgClRingObj ℓ) L.obj
      ((centreMap g I).left z') := by
  obtain ⟨U', hzU', hL⟩ := h
  exact ⟨(centreMap g I).left ''ᵁ U', ⟨z', hzU', rfl⟩,
    isZero_restrict_specializationDefect_image k' I g L U' hL⟩

/-- **Reduction of blueprint `lemma-vanishing-generic-points-principal-divisor--1` to neighbourhoods
of the generic points**: suppose that for every generic point `ζ` of an irreducible component of `Z`
there are an open immersion `g : V ⟶ X` and a point `ζ'` of `Z ∩ V` over `ζ` such that the defect
`C_{V, Z ∩ V}(g^* L)` vanishes near `ζ'`. Then there is a dense open `U ⊆ Z` over which
`C_{X,Z}(L)` vanishes. -/
theorem exists_dense_isZero_specializationDefect_of_forall_isOpenImmersion
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h : ∀ ζ : (centre X I).left, closure {ζ} ∈ irreducibleComponents (centre X I).left →
      ∃ (V : Over (Spec (.of k))) (_ : LocallyOfFiniteType V.hom) (_ : QuasiCompact V.hom)
        (_ : IsSeparated V.hom) (g : V ⟶ X) (_ : IsOpenImmersion g.left)
        (ζ' : (centre V (I.comap g.left)).left), (centreMap g I).left ζ' = ζ ∧
        defectVanishesNear V (I.comap g.left) k' (Profinite.padicAlgClRingObj ℓ)
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj L).obj ζ') :
    ∃ U : (centre X I).left.Opens, Dense (U : Set (centre X I).left) ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj)) := by
  refine genericallyVanishingDefect_of_forall_defectVanishesNear X I k' _ L.obj fun ζ hζ ↦ ?_
  obtain ⟨V, _, _, _, g, _, ζ', rfl, hV⟩ := h ζ hζ
  exact defectVanishesNear_of_isOpenImmersion I k' g L ζ' hV

end AlgebraicGeometry.ProEtale.CondensedRing
