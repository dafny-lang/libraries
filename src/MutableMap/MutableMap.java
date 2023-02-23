/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/
package DafnyLibraries;

import dafny.DafnySet;
import dafny.DafnyMap;
import dafny.Tuple2;
import dafny.TypeDescriptor;
import dafny.Helpers;

import java.util.concurrent.*;
import java.util.ArrayList;
import java.util.Map;
import java.math.BigInteger;

public class MutableMap<K,V> {
  private ConcurrentHashMap<K,V> m;

  public DafnyMap<K,V> Content() {
    return new DafnyMap<K,V>(m);
  }

  public MutableMap() {
    m = new ConcurrentHashMap<K,V>();
  }

  public MutableMap(TypeDescriptor<K> x, TypeDescriptor<V> y) {
    m = new ConcurrentHashMap<K,V>();
  }

  public void Put(K k, V v) {
    m.put(k, v);
  }

  public DafnySet<? extends K> Keys() {
    return new DafnySet(m.keySet());
  }

  public boolean HasKey(K k) {
    return m.containsKey(k);
  }

  public DafnySet<? extends V> Values() {
    return new DafnySet(m.values());
  }

  public DafnySet<? extends Tuple2<K,V>> Items() {
    ArrayList<Tuple2<K, V>> list = new ArrayList<Tuple2<K, V>>();
    for (Map.Entry<K, V> entry : m.entrySet()) {
      list.add(new Tuple2<K, V>(entry.getKey(), entry.getValue()));
    }
    return new DafnySet<Tuple2<K, V>>(list);
  }

  public V Select(K k) {
    return m.get(k);
  }

  public void Remove(K k) {
    m.remove(k);
  }

  public BigInteger Size() {
    return BigInteger.valueOf(m.size());
  }
}