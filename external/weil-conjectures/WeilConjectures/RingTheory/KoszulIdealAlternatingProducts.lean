/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulConormalCyclePresentation
import WeilConjectures.RingTheory.KoszulAugmentationLiftExists
import WeilConjectures.RingTheory.KoszulAugmentationLiftHomotopy
import WeilConjectures.RingTheory.KoszulGeneratorChainMap

/-! # Alternating Koszul products before conormal descent

Source: Stacks Project, Tags 09PQ and 00LS.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

private theorem tensorKoszul_d_zero (A : Type u) [CommRing A]
    (I : Ideal A) (r : ℕ) (g : Fin r → I) (i j : ℕ) :
    (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
      (ExteriorAlgebra.koszulComplex A r (fun k ↦ (g k : A)))).d i j = 0 := by
  classical
  by_cases hij : i = j + 1
  · subst i
    change (tensorRight (ModuleCat.of A (A ⧸ I))).map
      ((ExteriorAlgebra.koszulComplex A r (fun k ↦ (g k : A))).d (j + 1) j) = 0
    simp only [ExteriorAlgebra.koszulComplex, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply LinearMap.ext
    intro y
    change TensorProduct.tmul A
      (ExteriorAlgebra.koszulBoundary A r (fun k ↦ (g k : A)) j
        (exteriorPower.ιMulti A (j + 1) v)) y = 0
    rw [ExteriorAlgebra.boundary_wedge, TensorProduct.sum_tmul]
    apply Finset.sum_eq_zero
    intro k hk
    rw [TensorProduct.smul_tmul]
    have he : Finsupp.linearCombination A (fun k ↦ (g k : A)) =
        I.subtype.comp (Finsupp.linearCombination A g) := by
      ext k
      simp
    have hmem : Finsupp.linearCombination A (fun k ↦ (g k : A)) (v k) ∈ I := by
      rw [he]
      exact (Finsupp.linearCombination A g (v k)).property
    have hz : (((-1 : A) ^ (k.val + 2) *
        Finsupp.linearCombination A (fun k ↦ (g k : A)) (v k)) • y : A ⧸ I) = 0 := by
      change Ideal.Quotient.mk I _ * y = 0
      rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, mul_zero, zero_mul]
    rw [hz, TensorProduct.tmul_zero]
  · have hz := (ExteriorAlgebra.koszulComplex A r (fun k ↦ (g k : A))).shape i j
      (by simpa [eq_comm] using hij)
    change (tensorRight (ModuleCat.of A (A ⧸ I))).map
      ((ExteriorAlgebra.koszulComplex A r (fun k ↦ (g k : A))).d i j) = 0
    rw [hz, Functor.map_zero]

private noncomputable def wedgeCycles (A : Type u) [CommRing A]
    (I : Ideal A) (r n : ℕ) (g : Fin r → I) :
    (⋀[A]^n (Fin r →₀ A)) →ₗ[A]
      ((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
        (ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)))).cycles n) :=
  let K := (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
    (ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A))))
  ((K.iCyclesIso n ((ComplexShape.down ℕ).next n) rfl
    (tensorKoszul_d_zero A I r g n _)).inv.hom).comp
      ((TensorProduct.mk A (⋀[A]^n (Fin r →₀ A)) (A ⧸ I)).flip 1)

private theorem wedgeCycles_spec (A : Type u) [CommRing A]
    (I : Ideal A) (r n : ℕ) (g : Fin r → I) (x : ⋀[A]^n (Fin r →₀ A)) :
    (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
      (ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)))).iCycles n
        (wedgeCycles A I r n g x) = TensorProduct.tmul A x (1 : A ⧸ I) := by
  let K := (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
    (ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A))))
  exact congrArg (fun f ↦ f (TensorProduct.tmul A x (1 : A ⧸ I)))
    (K.iCyclesIso_inv_hom_id n _ rfl (tensorKoszul_d_zero A I r g n _))

private noncomputable def wedgeEval (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (r : ℕ) (g : Fin r → I)
    (a : ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex) :
    (⋀[A]^n (Fin r →₀ A)) →ₗ[A]
      ((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
        P.complex).homology n) :=
  let T := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
  (((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
    (T.map a)).hom.comp ((T.obj
      (ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)))).homologyπ n).hom).comp
        (wedgeCycles A I r n g)

private theorem generatorMap_exists (A : Type u) [CommRing A]
    (r s : ℕ) (f : Fin r → A) (g : Fin s → A)
    (t : (Fin r →₀ A) →ₗ[A] (Fin s →₀ A))
    (ht : (Finsupp.linearCombination A g).comp t = Finsupp.linearCombination A f) :
    ∃ U : ExteriorAlgebra.koszulComplex A r f ⟶ ExteriorAlgebra.koszulComplex A s g,
      ∀ n, U.f n = ModuleCat.ofHom (exteriorPower.map n t) := by
  have hd (r : ℕ) (k : Fin r → A) (n : ℕ) :
      (ExteriorAlgebra.koszulComplex A r k).d (n + 1) n =
        ModuleCat.ofHom (ExteriorAlgebra.koszulBoundary A r k n) := by
    dsimp only [ExteriorAlgebra.koszulComplex]
    exact ChainComplex.of_d _ _ n
  have hcomm (n : ℕ) :
      (ExteriorAlgebra.koszulBoundary A s g n).comp (exteriorPower.map (n + 1) t) =
      (exteriorPower.map n t).comp (ExteriorAlgebra.koszulBoundary A r f n) := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, ExteriorAlgebra.boundary_wedge, map_sum, map_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Function.comp_apply]
    rw [show Finsupp.linearCombination A g (t (v i)) =
      Finsupp.linearCombination A f (v i) from LinearMap.congr_fun ht (v i)]
    rfl
  refine ⟨ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (exteriorPower.map n t)) ?_,
    fun n ↦ rfl⟩
  intro n
  rw [hd s g n, hd r f n]
  exact ModuleCat.hom_ext (hcomm n)

private theorem wedgeEval_naturality (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (r s : ℕ) (f : Fin r → I) (g : Fin s → I)
    (a : ExteriorAlgebra.koszulComplex A r (fun j ↦ (f j : A)) ⟶ P.complex)
    (b : ExteriorAlgebra.koszulComplex A s (fun j ↦ (g j : A)) ⟶ P.complex)
    (ha : a.f 0 ≫ P.π.f 0 = ModuleCat.ofHom (I.mkQ.comp
      (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap))
    (hb : b.f 0 ≫ P.π.f 0 = ModuleCat.ofHom (I.mkQ.comp
      (exteriorPower.zeroEquiv A (Fin s →₀ A)).toLinearMap))
    (t : (Fin r →₀ A) →ₗ[A] (Fin s →₀ A))
    (ht : (Finsupp.linearCombination A (fun j ↦ (g j : A))).comp t =
      Finsupp.linearCombination A (fun j ↦ (f j : A)))
    (x : ⋀[A]^n (Fin r →₀ A)) :
    wedgeEval A I n P r f a x =
      wedgeEval A I n P s g b (exteriorPower.map n t x) := by
  obtain ⟨U, hU⟩ := generatorMap_exists A r s
    (fun j ↦ (f j : A)) (fun j ↦ (g j : A)) t ht
  have haug : (U ≫ b).f 0 ≫ P.π.f 0 = a.f 0 ≫ P.π.f 0 := by
    change U.f 0 ≫ b.f 0 ≫ P.π.f 0 = _
    rw [hb, ha, hU]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change I.mkQ (exteriorPower.zeroEquiv A (Fin s →₀ A)
      (exteriorPower.map 0 t y)) = I.mkQ (exteriorPower.zeroEquiv A (Fin r →₀ A) y)
    exact congrArg I.mkQ (LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality t) y)
  obtain ⟨h⟩ := koszul_augmentation_lifts_homotopic A I r f P a (U ≫ b) haug.symm
  let T := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n
  let Kf := T.obj (ExteriorAlgebra.koszulComplex A r (fun j ↦ (f j : A)))
  let Kg := T.obj (ExteriorAlgebra.koszulComplex A s (fun j ↦ (g j : A)))
  have heq : H.map (T.map a) = H.map (T.map (U ≫ b)) :=
    ((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomotopy h).homologyMap_eq n
  have hc : HomologicalComplex.cyclesMap (T.map U) n (wedgeCycles A I r n f x) =
      wedgeCycles A I s n g (exteriorPower.map n t x) := by
    apply (ModuleCat.mono_iff_injective (Kg.iCycles n)).mp inferInstance
    have hi := congrArg (fun k ↦ k (wedgeCycles A I r n f x))
      (HomologicalComplex.cyclesMap_i (T.map U) n)
    change Kg.iCycles n (HomologicalComplex.cyclesMap (T.map U) n
      (wedgeCycles A I r n f x)) = (T.map U).f n
        (Kf.iCycles n (wedgeCycles A I r n f x)) at hi
    rw [hi, wedgeCycles_spec, wedgeCycles_spec]
    change (tensorRight (ModuleCat.of A (A ⧸ I))).map (U.f n)
      (TensorProduct.tmul A x (1 : A ⧸ I)) = _
    rw [hU]
    rfl
  have hn := congrArg (fun k ↦ k (wedgeCycles A I r n f x))
    (HomologicalComplex.homologyπ_naturality (T.map U) n)
  change H.map (T.map U) (Kf.homologyπ n (wedgeCycles A I r n f x)) =
    Kg.homologyπ n (HomologicalComplex.cyclesMap (T.map U) n
      (wedgeCycles A I r n f x)) at hn
  change H.map (T.map a) (Kf.homologyπ n (wedgeCycles A I r n f x)) =
    H.map (T.map b) (Kg.homologyπ n
      (wedgeCycles A I s n g (exteriorPower.map n t x)))
  rw [heq, Functor.map_comp, Functor.map_comp]
  change H.map (T.map b) (H.map (T.map U)
    (Kf.homologyπ n (wedgeCycles A I r n f x))) = _
  rw [hn, hc]

private theorem wedgeEval_torsion (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (r : ℕ) (g : Fin r → I)
    (b : ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex)
    (x : ⋀[A]^n (Fin r →₀ A)) :
    wedgeEval A I n P r g b x ∈ Submodule.torsionBySet A _ (I : Set A) := by
  rw [Submodule.mem_torsionBySet_iff]
  intro a
  have hz : (a : A) • wedgeCycles A I r n g x = 0 := by
    apply (ModuleCat.mono_iff_injective
      (((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
        (ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A))))).iCycles n)).mp
          inferInstance
    rw [map_smul, wedgeCycles_spec, map_zero]
    change (a : A) • (TensorProduct.tmul A x (1 : A ⧸ I)) = 0
    rw [← TensorProduct.tmul_smul]
    have ha : (a : A) • (1 : A ⧸ I) = 0 := by
      change Ideal.Quotient.mk I (a : A) * 1 = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr a.property, zero_mul]
    rw [ha, TensorProduct.tmul_zero]
  let T := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
  let L := ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
    (T.map b)).hom.comp ((T.obj
      (ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)))).homologyπ n).hom
  change (a : A) • L (wedgeCycles A I r n g x) = 0
  rw [← L.map_smul, hz, L.map_zero]

private theorem linearCombination_update (A : Type u) [CommRing A]
    (I : Ideal A) (r n : ℕ) (g : Fin r → I) (v : Fin n → (Fin r →₀ A))
    (i : Fin n) (x : Fin r →₀ A) :
    (fun j ↦ Finsupp.linearCombination A g (Function.update v i x j)) =
      Function.update (fun j ↦ Finsupp.linearCombination A g (v j)) i
        (Finsupp.linearCombination A g x) := by
  ext j
  by_cases hj : j = i <;> simp [hj]

/-- Before descent modulo I², ideal elements have alternating products in the
I-annihilated part of resolution homology, realized by a suitable family of
Koszul maps. No factorization through the conormal module is asserted.
Source: Stacks Project, Tag 09PQ, Lemma 23.6.12; Tag 00LS, part (1).
(blueprint: new-t4-koszul-ideal-alternating-products).

Proof: Take a free strictly commutative Tate resolution Q of A/I. For each x
in I choose a degree-one lift with differential x. Its class after tensoring
is independent of the lift: the difference is a cycle in Q, hence a boundary.
Adding or scaling lifts proves A-linearity of this assignment on I, without
yet identifying its kernel. Multiply n such classes in Q tensor A/I. The
product is multilinear and alternating, since odd elements square to zero
in a strictly commutative Tate algebra, also in characteristic two. Each
class is annihilated by I because the tensor factor A/I is. Compare Q with P
by an augmentation-preserving map and transport the products on homology;
this gives F with values in the I-torsion submodule. For each tuple g send
the Koszul generators to its chosen degree-one lifts in Q and compose with
the comparison to P. These maps b preserve augmentation and evaluate each
wedge as the product defining F. Linearity handles arbitrary vectors v.
The actual cycle z is unique for its prescribed image since iCycles is
monic. For n=0 use the empty product, the quotient unit, which is still
annihilated by I. If I=A the homology is zero; I=0 and characteristic two
need no exclusions. Descent modulo I² and independence from the chosen
family b are proved separately in KoszulConormalCycleRelations. -/
theorem koszul_ideal_alternating_products (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I))) :
    ∃ (b : ∀ (r : ℕ) (g : Fin r → I),
      ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex)
      (F : I [⋀^Fin n]→ₗ[A]
        (Submodule.torsionBySet A
          ((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
            P.complex).homology n) (I : Set A))),
      (∀ (r : ℕ) (g : Fin r → I), (b r g).f 0 ≫ P.π.f 0 =
        ModuleCat.ofHom (I.mkQ.comp
          (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap)) ∧
      (∀ s : KoszulConormalWedgeCycle A I n,
        (F (fun j ↦ Finsupp.linearCombination A s.g (s.v j))).val =
          ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
            (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).map
              (b s.r s.g)))
            ((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
              (.down ℕ)).obj
              (ExteriorAlgebra.koszulComplex A s.r
                (fun j ↦ (s.g j : A)))).homologyπ n s.z)) := by
  classical
  -- Any augmentation-preserving family works, by homotopy uniqueness.
  choose b hb using fun r g ↦ koszul_augmentation_lift_exists A I r g P
  let e : Fin n → (Fin n →₀ A) := fun j ↦ Finsupp.single j 1
  let ev := fun w : Fin n → I ↦
    wedgeEval A I n P n w (b n w) (exteriorPower.ιMulti A n e)
  -- Substitute arbitrary vectors into the Koszul complex on their ideal combinations.
  have hformula (r : ℕ) (g : Fin r → I) (v : Fin n → (Fin r →₀ A)) :
      ev (fun j ↦ Finsupp.linearCombination A g (v j)) =
        wedgeEval A I n P r g (b r g) (exteriorPower.ιMulti A n v) := by
    let w : Fin n → I := fun j ↦ Finsupp.linearCombination A g (v j)
    let t := Finsupp.linearCombination A v
    have ht : (Finsupp.linearCombination A (fun j ↦ (g j : A))).comp t =
        Finsupp.linearCombination A (fun j ↦ (w j : A)) := by
      ext j
      simp only [LinearMap.comp_apply, t, Finsupp.lsingle_apply,
        Finsupp.linearCombination_single, one_smul]
      exact (Finsupp.apply_linearCombination A I.subtype g (v j)).symm
    have he : t ∘ e = v := by
      ext j
      simp [t, e]
    change wedgeEval A I n P n w (b n w) (exteriorPower.ιMulti A n e) = _
    rw [wedgeEval_naturality A I n P n r w g (b n w) (b r g)
      (hb n w) (hb r g) t ht, exteriorPower.map_apply_ιMulti, he]
  -- Put both summands in one larger tuple and use linearity of its exterior wedge.
  have hadd (w : Fin n → I) (i : Fin n) (x y : I) :
      ev (Function.update w i (x + y)) =
        ev (Function.update w i x) + ev (Function.update w i y) := by
    let g : Fin (n + 1) → I := Fin.lastCases y (Function.update w i x)
    let v : Fin n → (Fin (n + 1) →₀ A) := fun j ↦ Finsupp.single j.castSucc 1
    let z : Fin (n + 1) →₀ A := Finsupp.single (Fin.last n) 1
    have hv : (fun j ↦ Finsupp.linearCombination A g (v j)) =
        Function.update w i x := by
      ext j
      simp [g, v]
    have hz : Finsupp.linearCombination A g z = y := by simp [g, z]
    have hvi : Finsupp.linearCombination A g (v i) = x := by simp [g, v]
    have hsub (a : Fin (n + 1) →₀ A) :
        ev (Function.update w i (Finsupp.linearCombination A g a)) =
          wedgeEval A I n P (n + 1) g (b (n + 1) g)
            (exteriorPower.ιMulti A n (Function.update v i a)) := by
      have h := hformula (n + 1) g (Function.update v i a)
      rw [linearCombination_update, hv, Function.update_idem] at h
      exact h
    rw [← hvi, ← hz, ← map_add, hsub, hsub, hsub,
      (exteriorPower.ιMulti A n).map_update_add, map_add]
  have hsmul (w : Fin n → I) (i : Fin n) (c : A) (x : I) :
      ev (Function.update w i (c • x)) = c • ev (Function.update w i x) := by
    let g := Function.update w i x
    have hv : (fun j ↦ Finsupp.linearCombination A g (e j)) = g := by
      ext j
      simp [e]
    have hi : Finsupp.linearCombination A g (e i) = x := by simp [e, g]
    have h := hformula n g (Function.update e i (c • e i))
    rw [linearCombination_update, hv, map_smul, hi, Function.update_idem] at h
    rw [h, (exteriorPower.ιMulti A n).map_update_smul, map_smul,
      Function.update_eq_self]
  -- Equal ideal entries can be represented by equal vectors in one source complex.
  have halt (w : Fin n → I) (i j : Fin n) (hij : w i = w j) (hne : i ≠ j) :
      ev w = 0 := by
    have ht : (fun k ↦ Finsupp.linearCombination A w
        (Function.update e j (e i) k)) = w := by
      ext k
      by_cases hk : k = j
      · subst k
        simp [e, hij]
      · simp [hk, e]
    have h := hformula n w (Function.update e j (e i))
    rw [ht] at h
    rw [h, (exteriorPower.ιMulti A n).map_eq_zero_of_eq _
      (by simp [hne]) hne, map_zero]
  let F₀ : I [⋀^Fin n]→ₗ[A]
      ((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
        P.complex).homology n) :=
    { toFun := ev
      map_update_add' := by
        intro inst w i x y
        cases Subsingleton.elim inst (instDecidableEqFin n)
        exact hadd w i x y
      map_update_smul' := by
        intro inst w i c x
        cases Subsingleton.elim inst (instDecidableEqFin n)
        exact hsmul w i c x
      map_eq_zero_of_eq' := halt }
  let F := F₀.codRestrict (Submodule.torsionBySet A _ (I : Set A))
    (fun w ↦ wedgeEval_torsion A I n P n w (b n w) (exteriorPower.ιMulti A n e))
  refine ⟨b, F, hb, ?_⟩
  intro s
  change ev (fun j ↦ Finsupp.linearCombination A s.g (s.v j)) = _
  rw [hformula]
  have hz : wedgeCycles A I s.r n s.g (exteriorPower.ιMulti A n s.v) = s.z := by
    apply (ModuleCat.mono_iff_injective
      (((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
        (ExteriorAlgebra.koszulComplex A s.r (fun j ↦ (s.g j : A))))).iCycles n)).mp
          inferInstance
    rw [wedgeCycles_spec, s.hz]
  exact congrArg (fun z ↦
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
      (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).map
        (b s.r s.g)))
      ((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
        (ExteriorAlgebra.koszulComplex A s.r (fun j ↦ (s.g j : A)))).homologyπ n z)) hz

end AlgebraicGeometry
