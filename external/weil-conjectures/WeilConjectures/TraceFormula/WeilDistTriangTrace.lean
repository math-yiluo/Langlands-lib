/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.WeilDistTriang
public import WeilConjectures.TraceFormula.WeilDistTriangHomology
public import WeilConjectures.TraceFormula.WeilTrace
public import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree

/-!

# Additivity of the local trace along distinguished triangles of Weil objects

For a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` of Weil objects
(`ProEtale.CondensedRing.WeilBoundedConstructible.IsDistTriang`), the local traces satisfy
`t_{n+1}(B; x̄) = t_{n+1}(A; x̄) + t_{n+1}(C; x̄)`
(`ProEtale.CondensedRing.weilStalkTraceAlternatingSum_eq_add_of_isDistTriang`).

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor MonoidalCategory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] in
/-- The stalk at `x̄` of a Weil sheaf, with its Frobenius operator, is finite free as soon as the
pullback `x̄^* F` is. The ring structure on `k̄` is that of `AlgebraicClosure.instCommRing` in
`x̄^* F` and that of the field `k̄` in the stalk; the transport between the two is done through
an equation of ring structures, the kernel being unable to identify them inside the pullbacks. -/
lemma isFiniteFree_frobeniusStalk_carrier {e : Y ≅ Y} (n : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ Y.left)
    (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x)
    (F : WeilSheaf ℓ e)
    (hF : letI := Abelian.hasFiniteBiproducts (C := GeometricPointMod ℓ (AlgebraicClosure k))
      IsFiniteFree ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj F.carrier)) :
    letI := Abelian.hasFiniteBiproducts (C := GeometricPointMod ℓ (AlgebraicClosure k))
    IsFiniteFree (WeilSheaf.frobeniusStalk ℓ (n + 1) x hx F).carrier := by
  have key (R : CommRing (AlgebraicClosure k)) (_ : R = AlgebraicClosure.instCommRing k)
      (x' : Spec (@CommRingCat.of (AlgebraicClosure k) R) ⟶ Y.left) (_ : HEq x' x) :
      IsFiniteFree ((x')^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj F.carrier) := by
    subst R
    obtain rfl := eq_of_heq ‹HEq x' x›
    exact hF
  rw [WeilSheaf.frobeniusStalk, WeilSheaf.powStalkFunctor, Functor.comp_obj,
    WeilSheaf.stalkFunctor_obj_carrier, WeilSheaf.powFunctor_obj, WeilSheaf.pow_carrier]
  exact key Field.toCommRing rfl x HEq.rfl

section Stalk

variable {e : Y ≅ Y} (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ Y.left)
  (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x)

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The stalk at `x̄` of a Weil sheaf with zero underlying sheaf is zero. -/
lemma isZero_frobeniusStalk_carrier {F : WeilSheaf ℓ e} (hF : IsZero F.carrier) :
    IsZero (WeilSheaf.frobeniusStalk ℓ (n + 1) x hx F).carrier := by
  rw [WeilSheaf.frobeniusStalk, WeilSheaf.powStalkFunctor, Functor.comp_obj,
    WeilSheaf.stalkFunctor_obj_carrier, WeilSheaf.powFunctor_obj, WeilSheaf.pow_carrier]
  exact Functor.map_isZero _ hF

/-- The stalk functor at `x̄` preserves exact sequences of Weil sheaves. -/
lemma exists_exact_powStalkFunctor_map {F G H : WeilSheaf ℓ e} (f : F ⟶ G) (g : G ⟶ H)
    {w : f.hom.f ≫ g.hom.f = 0} (hS : (ShortComplex.mk _ _ w).Exact) :
    ∃ w' : ((WeilSheaf.powStalkFunctor ℓ (n + 1) x hx).map f).hom.f ≫
      ((WeilSheaf.powStalkFunctor ℓ (n + 1) x hx).map g).hom.f = 0,
      (ShortComplex.mk _ _ w').Exact :=
  ⟨(ShortComplex.map (ShortComplex.mk _ _ w) (@upperStar (Profinite.padicAlgClRingObj ℓ) _ _
    (Spec (@CommRingCat.of (AlgebraicClosure k) Field.toCommRing)) Y.left x)).zero,
    hS.map (@upperStar (Profinite.padicAlgClRingObj ℓ) _ _
      (Spec (@CommRingCat.of (AlgebraicClosure k) Field.toCommRing)) Y.left x)⟩

/-- The Frobenius operators on the stalks at `x̄` commute with the morphisms induced by
morphisms of Weil sheaves. -/
lemma frobeniusStalk_str_hom_comp {F G : WeilSheaf ℓ e} (φ : F ⟶ G) :
    (WeilSheaf.frobeniusStalk ℓ (n + 1) x hx F).str.hom ≫
        ((WeilSheaf.powStalkFunctor ℓ (n + 1) x hx).map φ).hom.f =
      ((WeilSheaf.powStalkFunctor ℓ (n + 1) x hx).map φ).hom.f ≫
        (WeilSheaf.frobeniusStalk ℓ (n + 1) x hx G).str.hom :=
  ((WeilSheaf.powStalkFunctor ℓ (n + 1) x hx).map φ).hom.h.symm

end Stalk

/-- **Additivity of the local trace along distinguished triangles, for finite free stalks.**
Assume that `End (𝟙_ Mod_{Spec k̄})` is a field and that the stalks at `x̄` of the homology sheaves
of Weil objects are finite free. Then for a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` of Weil
objects for `e`, `t_{n+1}(B; x̄) = t_{n+1}(A; x̄) + t_{n+1}(C; x̄)`: the homology sheaves form a
long exact sequence of Weil sheaves, whose stalks at `x̄` form a long exact sequence with the
Frobenius operators commuting with all the maps (`superTrace_eq_add_of_exact`). -/
theorem weilStalkTraceAlternatingSum_eq_add_of_isDistTriang_of_isFiniteFree {e : Y ≅ Y} (n : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ Y.left)
    (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x)
    (hK : ∀ t : End (𝟙_ (GeometricPointMod ℓ (AlgebraicClosure k))), t ≠ 0 → IsIso t.asHom)
    (h₁ : (1 : End (𝟙_ (GeometricPointMod ℓ (AlgebraicClosure k)))) ≠ 0)
    (hfree : ∀ (K : WeilBoundedConstructible ℓ e.hom) (j : ℤ),
      letI := Abelian.hasFiniteBiproducts (C := GeometricPointMod ℓ (AlgebraicClosure k))
      IsFiniteFree ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj
        ((DerivedCategory.homologyFunctor _ j).obj K.carrier.obj)))
    {A B C : WeilBoundedConstructible ℓ e.hom} {a : A ⟶ B} {b : B ⟶ C}
    (h : WeilBoundedConstructible.IsDistTriang ℓ a b) :
    weilStalkTraceAlternatingSum ℓ (n + 1) x hx B =
      weilStalkTraceAlternatingSum ℓ (n + 1) x hx A +
        weilStalkTraceAlternatingSum ℓ (n + 1) x hx C := by
  obtain ⟨δ, hT, hδ⟩ := h
  obtain ⟨⟨a₁, b₁, hbA⟩, -⟩ := (mem_boundedConstructible_iff _ _).1 A.carrier.property
  obtain ⟨⟨a₂, b₂, hbB⟩, -⟩ := (mem_boundedConstructible_iff _ _).1 B.carrier.property
  obtain ⟨⟨a₃, b₃, hbC⟩, -⟩ := (mem_boundedConstructible_iff _ _).1 C.carrier.property
  have e₁ (j : ℤ) := exists_exact_powStalkFunctor_map ℓ n x hx
    ((WeilBoundedConstructible.homologyFunctor ℓ e j).map a)
    ((WeilBoundedConstructible.homologyFunctor ℓ e j).map b)
    (DerivedCategory.HomologySequence.exact₂ _ hT j)
  have e₂ (j : ℤ) := exists_exact_powStalkFunctor_map ℓ n x hx
    ((WeilBoundedConstructible.homologyFunctor ℓ e j).map b)
    (WeilBoundedConstructible.homologyδ ℓ δ hδ j (j + 1) (add_comm 1 j))
    (DerivedCategory.HomologySequence.exact₃ _ hT j (j + 1) rfl)
  have e₃ (j : ℤ) := exists_exact_powStalkFunctor_map ℓ n x hx
    (WeilBoundedConstructible.homologyδ ℓ δ hδ j (j + 1) (add_comm 1 j))
    ((WeilBoundedConstructible.homologyFunctor ℓ e (j + 1)).map a)
    (DerivedCategory.HomologySequence.exact₁ _ hT j (j + 1) rfl)
  exact superTrace_eq_add_of_exact hK h₁
    (A := fun j ↦ (WeilSheaf.frobeniusStalk ℓ (n + 1) x hx
      ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj A)).carrier)
    (B := fun j ↦ (WeilSheaf.frobeniusStalk ℓ (n + 1) x hx
      ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj B)).carrier)
    (D := fun j ↦ (WeilSheaf.frobeniusStalk ℓ (n + 1) x hx
      ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj C)).carrier)
    (fun j ↦ (WeilSheaf.frobeniusStalk ℓ (n + 1) x hx
      ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj A)).str.hom)
    (fun j ↦ (WeilSheaf.frobeniusStalk ℓ (n + 1) x hx
      ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj B)).str.hom)
    (fun j ↦ (WeilSheaf.frobeniusStalk ℓ (n + 1) x hx
      ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj C)).str.hom)
    _ _ _
    (fun j ↦ frobeniusStalk_str_hom_comp ℓ n x hx _)
    (fun j ↦ frobeniusStalk_str_hom_comp ℓ n x hx _)
    (fun j ↦ frobeniusStalk_str_hom_comp ℓ n x hx
      (WeilBoundedConstructible.homologyδ ℓ δ hδ j (j + 1) (add_comm 1 j)))
    (fun j ↦ (e₁ j).fst) (fun j ↦ (e₂ j).fst) (fun j ↦ (e₃ j).fst)
    (fun j ↦ (e₁ j).snd) (fun j ↦ (e₂ j).snd) (fun j ↦ (e₃ j).snd)
    (fun j ↦ isFiniteFree_frobeniusStalk_carrier ℓ n x hx _ (hfree A j))
    (fun j ↦ isFiniteFree_frobeniusStalk_carrier ℓ n x hx _ (hfree B j))
    (fun j ↦ isFiniteFree_frobeniusStalk_carrier ℓ n x hx _ (hfree C j))
    ⟨min a₁ (min a₂ a₃), max b₁ (max b₂ b₃), fun j hj ↦
      ⟨isZero_frobeniusStalk_carrier ℓ n x hx (hbA j (by omega)),
        isZero_frobeniusStalk_carrier ℓ n x hx (hbB j (by omega)),
        isZero_frobeniusStalk_carrier ℓ n x hx (hbC j (by omega))⟩⟩

/-- **Additivity of the local trace along distinguished triangles of Weil objects**: for a
distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` of Weil objects for `e`,
`t_{n+1}(B; x̄) = t_{n+1}(A; x̄) + t_{n+1}(C; x̄)`. The long exact sequence of homology sheaves
`Hʲ(A) ⟶ Hʲ(B) ⟶ Hʲ(C) ⟶ Hʲ⁺¹(A)` is one of Weil sheaves, the connecting morphisms commuting with
the Frobenius structures; the stalk functor at `x̄` is exact, the stalks of the homology sheaves of
constructible complexes are finite free (`isFiniteFree_upperStar_homology`), and the
alternating sum of the traces of compatible endomorphisms of a bounded long exact sequence of finite
free objects vanishes (`superTrace_eq_add_of_exact`). -/
theorem weilStalkTraceAlternatingSum_eq_add_of_isDistTriang {e : Y ≅ Y} (n : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ Y.left)
    (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x)
    {A B C : WeilBoundedConstructible ℓ e.hom} {a : A ⟶ B} {b : B ⟶ C}
    (h : WeilBoundedConstructible.IsDistTriang ℓ a b) :
    weilStalkTraceAlternatingSum ℓ (n + 1) x hx B =
      weilStalkTraceAlternatingSum ℓ (n + 1) x hx A + weilStalkTraceAlternatingSum ℓ (n + 1) x hx C
          :=
  weilStalkTraceAlternatingSum_eq_add_of_isDistTriang_of_isFiniteFree ℓ n x hx
    (isIso_of_ne_zero_end_tensorUnit ℓ (instΩ := AlgebraicClosure.instCommRing k)
      (Field.toIsField _) IsField.isSepClosed_toField)
    (one_ne_zero_end_tensorUnit ℓ (instΩ := AlgebraicClosure.instCommRing k)
      (Field.toIsField _) IsField.isSepClosed_toField)
    (fun K j ↦ isFiniteFree_upperStar_homology ℓ (instΩ := AlgebraicClosure.instCommRing k)
      (Field.toIsField _) IsField.isSepClosed_toField K.carrier j x) h

end AlgebraicGeometry.ProEtale.CondensedRing
