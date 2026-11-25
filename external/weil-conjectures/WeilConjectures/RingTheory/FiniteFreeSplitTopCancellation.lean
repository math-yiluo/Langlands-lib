/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Cancelling a split top differential of a finite free complex

Source: Stacks Project, More on Algebra, Tag 064U, finite-free replacement construction
(blueprint: lem-pc-finite-free-split-top-cancellation).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

/-- Transport finite freeness along an isomorphism of modules. -/
private theorem freeFinite_iso {R : Type u} [CommRing R] {M N : ModuleCat.{v} R}
    (e : M ≅ N) (h : Module.Free R N ∧ Module.Finite R N) :
    Module.Free R M ∧ Module.Finite R M := by
  have : Module.Free R N := h.1
  have : Module.Finite R N := h.2
  exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv, Module.Finite.equiv e.symm.toLinearEquiv⟩

/-- A zero module is finite free, including over the zero ring. -/
private theorem freeFinite_zero {R : Type u} [CommRing R] {M : ModuleCat.{v} R}
    (h : IsZero M) : Module.Free R M ∧ Module.Finite R M := by
  have : Subsingleton M := ModuleCat.subsingleton_of_isZero h
  exact ⟨inferInstance, inferInstance⟩

/-- A binary biproduct of finite free modules is finite free. -/
private theorem freeFinite_biprod {R : Type u} [CommRing R] (M N : ModuleCat.{v} R)
    (hM : Module.Free R M ∧ Module.Finite R M)
    (hN : Module.Free R N ∧ Module.Finite R N) :
    Module.Free R (M ⊞ N : ModuleCat.{v} R) ∧
      Module.Finite R (M ⊞ N : ModuleCat.{v} R) := by
  have : Module.Free R M := hM.1
  have : Module.Finite R M := hM.2
  have : Module.Free R N := hN.1
  have : Module.Finite R N := hN.2
  apply freeFinite_iso (ModuleCat.biprodIsoProd M N)
  exact ⟨inferInstance, inferInstance⟩

/-- A split top differential can be cancelled while keeping every term finite free.
Source: Stacks Project, More on Algebra, Tag 064U, finite-free replacement construction,
with the split-summand cancellation in step 3 of
lem-pc-pseudo-coherent-bounded-finite-free-model
(blueprint: lem-pc-finite-free-split-top-cancellation).

Proof: Put `T = P.X n`, `A = P.X (n - 1)` and `d = P.d (n - 1) n`. The supplied
section splits `A` as `ker d ⊕ T`. Since `P` vanishes above `n`, remove the
contractible identity complex on `T` in degrees `n - 1,n`. The resulting complex
has top term `ker d` in degree `n - 1`; all lower terms agree with `P`. Add the
contractible identity complex on `T` in degrees `n - 2,n - 1`. Its new top term
is `ker d ⊕ T`, isomorphic to `A`, and its term in degree `n - 2` is
`P.X (n - 2) ⊕ T`. Thus every term is finite free and all terms above `n - 1`
vanish. Project off the newly added contractible summand and include the
remaining kernel summand into `P`. These are chain maps because `d² = 0`.
The composite is a quasi-isomorphism: the projection has contractible kernel,
and the inclusion has contractible cokernel. This argument also works when
`T` is zero, and places no lower bound on the complex. -/
theorem exists_finiteFree_cancel_split_top
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    (hbound : P.IsStrictlyLE n)
    (hfree : ∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i))
    (s : P.X n ⟶ P.X (n - 1)) (hs : s ≫ P.d (n - 1) n = 𝟙 (P.X n)) :
    ∃ (L : CochainComplex (ModuleCat.{v} R) ℤ) (π : L ⟶ P),
      L.IsStrictlyLE (n - 1) ∧
      (∀ i : ℤ, Module.Free R (L.X i) ∧ Module.Finite R (L.X i)) ∧
      QuasiIso π := by
  classical
  have : P.IsStrictlyLE n := hbound
  let m := n - 1
  change s ≫ P.d m n = 𝟙 (P.X n) at hs
  have hm : m + 1 = n := by dsimp [m]; omega
  have hnext : (ComplexShape.up ℤ).next m = n :=
    ComplexShape.next_eq' _ (show (ComplexShape.up ℤ).Rel m n from hm)
  let S := ShortComplex.mk (P.iCycles m) (P.d m n) (P.iCycles_d m n)
  have hS : S.Exact := S.exact_of_f_is_kernel (P.cyclesIsKernel m n hnext)
  let eSplit : P.cycles m ⊞ P.X n ≅ P.X m :=
    (ShortComplex.Splitting.ofExactOfSection S hS s hs inferInstance).isoBinaryBiproduct.symm
  let T := (CochainComplex.singleFunctor (ModuleCat.{v} R) m).obj (P.X n)
  let A := mappingCone (𝟙 T)
  let K := P.truncLE m
  let L := K ⊞ A
  have hAzero (i : ℤ) (hi : m < i) : IsZero (A.X i) := by
    apply (mappingCone.isZero_X_iff (𝟙 T) i).2
    exact ⟨T.isZero_of_isStrictlyLE m (i + 1) (by omega),
      T.isZero_of_isStrictlyLE m i hi⟩
  have hLbound : L.IsStrictlyLE m := by
    apply (L.isStrictlyLE_iff m).2
    intro i hi
    exact ((biprod_isZero_iff _ _).2
      ⟨K.isZero_of_isStrictlyLE m i hi, hAzero i hi⟩).of_iso (biprodXIso K A i)
  have eATop : A.X m ≅ P.X n :=
    homotopyCofiber.XIsoBiprod (𝟙 T) m (m + 1) rfl ≪≫
      (isoZeroBiprod (T.isZero_of_isStrictlyLE m (m + 1) (by omega))).symm ≪≫
        singleObjXSelf (ComplexShape.up ℤ) m (P.X n)
  have hTfree (i : ℤ) : Module.Free R (T.X i) ∧ Module.Finite R (T.X i) := by
    by_cases hi : i = m
    · subst i
      exact freeFinite_iso (singleObjXSelf (ComplexShape.up ℤ) m (P.X n)) (hfree n)
    · exact freeFinite_zero (isZero_single_obj_X (ComplexShape.up ℤ) m (P.X n) i hi)
  have hAfree (i : ℤ) : Module.Free R (A.X i) ∧ Module.Finite R (A.X i) :=
    freeFinite_iso (homotopyCofiber.XIsoBiprod (𝟙 T) i (i + 1) rfl)
      (freeFinite_biprod _ _ (hTfree (i + 1)) (hTfree i))
  have hLfree (i : ℤ) : Module.Free R (L.X i) ∧ Module.Finite R (L.X i) := by
    rcases lt_trichotomy i m with hi | hi | hi
    · exact freeFinite_iso (biprodXIso K A i)
        (freeFinite_biprod _ _ (freeFinite_iso (P.truncLEXIso m i hi) (hfree i))
          (hAfree i))
    · subst i
      exact freeFinite_iso
        (biprodXIso K A m ≪≫
          biprod.mapIso (P.truncLEXIsoCycles m) eATop ≪≫ eSplit) (hfree m)
    · exact freeFinite_zero (L.isZero_of_isStrictlyLE m i hi)
  have hepi : Epi (P.d m n) := ⟨fun f g h => by
    have := congrArg (fun k => s ≫ k) h
    simpa only [← Category.assoc, hs, Category.id_comp] using this⟩
  have hPle : P.IsLE m := by
    apply (P.isLE_iff m).2
    intro i hi
    by_cases hin : i = n
    · subst i
      have hprev : (ComplexShape.up ℤ).prev n = m :=
        ComplexShape.prev_eq' _ (show (ComplexShape.up ℤ).Rel m n from hm)
      have hd : (P.sc n).g = 0 := by
        exact (P.isZero_of_isStrictlyLE n ((ComplexShape.up ℤ).next n)
          (by rw [ComplexShape.next_eq' _ (ComplexShape.up_mk n (n + 1) rfl)]; omega)).eq_of_tgt _ _
      apply ((P.sc n).exact_iff_epi hd).2
      change Epi (P.d ((ComplexShape.up ℤ).prev n) n)
      rwa [hprev]
    · exact ShortComplex.exact_of_isZero_X₂ (P.sc i)
        (P.isZero_of_isStrictlyLE n i (by dsimp [m] at hi; omega))
  have : P.IsLE m := hPle
  have hπ : QuasiIso (biprod.fst : L ⟶ K) := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let F := HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) i
    have hz : IsZero (F.obj A) := by
      apply (IsZero.iff_id_eq_zero _).2
      change 𝟙 (A.homology i) = 0
      simpa using (mappingCone.homotopyToZeroOfId T).homologyMap_eq i
    have hmap : F.map (biprod.snd : L ⟶ A) = 0 := hz.eq_of_tgt _ _
    change IsIso (F.map (biprod.fst : L ⟶ K))
    refine ⟨⟨F.map (biprod.inl : K ⟶ L), ?_, ?_⟩⟩
    · have ht := congrArg F.map (biprod.total (X := K) (Y := A))
      rw [Functor.map_add, Functor.map_comp, Functor.map_comp, hmap,
        zero_comp, add_zero, CategoryTheory.Functor.map_id] at ht
      exact ht
    · simp [← Functor.map_comp]
  have : QuasiIso (biprod.fst : L ⟶ K) := hπ
  refine ⟨L, biprod.fst ≫ P.ιTruncLE m, hLbound, hLfree, ?_⟩
  infer_instance

end CochainComplex
