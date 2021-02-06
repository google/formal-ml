/-
Copyright 2020 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
 -/


import order.bounded_lattice

lemma with_top.not_none_lt {α:Type*} [preorder α] (a:with_top α):
  ¬(@has_lt.lt (with_top α) _  (none:with_top α) a):=
begin
  intro A1,
  rw lt_iff_le_not_le at A1,
  cases A1 with A1 A2,
  apply A2,
  apply with_top.le_none,
end

lemma with_top.not_none_le_some {α:Type*} [partial_order α] (a:α):
  ¬(@has_le.le (with_top α) _ (none) (some a)):=
begin
  intro A1,
  have B1:(some a) ≠ (none:with_top α),
  {
    simp,
  },
  have B3:(@has_le.le (with_top α) _ (some a) (none)) := with_top.le_none,
  have B4 := @le_antisymm (with_top α) _ (some a) (none) B3 A1,
  apply B1,
  apply B4
end
