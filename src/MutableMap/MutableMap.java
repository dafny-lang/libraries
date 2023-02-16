/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/
package MutableMap;

import dafny.DafnySet;
import dafny.DafnyMap;
import dafny.Tuple2;
import dafny.TypeDescriptor;

import java.util.HashMap;
import java.util.ArrayList;
import java.util.Map;


public class MutableMap<K,V> {
  private HashMap<K, V> m;

  public DafnyMap<K,V> content() {
    return new DafnyMap<>(m);
  }

  public MutableMap() {
    m = new HashMap<>();
  }

  public MutableMap(TypeDescriptor<K> x, TypeDescriptor<V> y) {
    m = new HashMap<>();
  }

  public void put(K k, V v) {
    m.put(k, v);
  }

  public DafnySet<? extends K> keys() {
    return new DafnySet<>(m.keySet());
  }

  public DafnySet<? extends V> values() {
    return new DafnySet<>(m.values());
  }

  public DafnySet<? extends Tuple2<K,V>> items() {
    ArrayList<Tuple2<K, V>> list = new ArrayList<Tuple2<K, V>>();
    for (Map.Entry<K, V> entry : m.entrySet()) {
      list.add(new Tuple2<K, V>(entry.getKey(), entry.getValue()));
    }
    return new DafnySet<Tuple2<K, V>>(list);
  }

  public V find(K k) {
    return m.get(k);
  }

  public void remove(K k) {
    m.remove(k);
  }

  public int size() {
    return m.size();
  }
}