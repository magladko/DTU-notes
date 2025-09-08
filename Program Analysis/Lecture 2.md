
### Activity 2
<div class="note activity"><h4 class="name">Match the method names.</h4><p>You might already have recognized that the method names form <code>jpamb.cases.Simple.assertPositive(I)V</code> a little language: <code class="red">jpamb.cases.Simple</code> <code>.</code> <code class="green">assertPositive</code> <code>:</code> <code class="orange">(I)</code> <code class="blue">V</code> where each part represent important information. The <span class="red">class</span>, the <span>method</span>, the <span class="orange">arguments</span>, and the <span class="blue">(return type)</span>.</p><p>Use <a href="https://regex101.com/"><code>https://regex101.com/</code></a> to try to match on the method. Here are some tricks:</p><ul><li><p>remember to pick the flavor that matches your implementation language (in the menu).</p></li><li><p>use the cases from <a href="https://github.com/kalhauge/jpamb/blob/main/stats/cases.txt"><code>https://github.com/kalhauge/jpamb/blob/main/stats/cases.txt</code></a> as test cases (you do that by inserting it in the big box).</p></li><li><p>you can use the quick references to help you write the expression.</p></li><li><p>remember that !'.' means everything, so use !'\.' to match !'.'.</p></li><li><p>use match groups to extract each part in your analysis.</p></li></ul></div>
```
(?<=\.)[a-z]+\w*(?=:)
```


### Activity 3
<div class="note activity"><h4 class="name">Extract the code</h4><p>Insert the code of <a href="https://github.com/kalhauge/jpamb/blob/main/src/main/java/jpamb/cases/Simple.java">jpamb.cases.Simple</a> into the <q>Test String</q> field, and try to extract the content of the methods.</p><div class="hint"><h4 class="hint-name">Hint (Hover to see)</h4><div class="hint-content"><pre><code class="language-python hljs" lang="python" data-highlighted="yes"><span class="hljs-string">r"public\W+static\W+(?P&lt;retype&gt;void)\W+(?P&lt;mname&gt;\w*)()\W*{(?P&lt;code&gt;[^}]*)}"</span></code></pre></div></div></div>

```
public\W+static\W+(?P<retype>(\w+))\W+(?P<mname>\w*)\W*\(\W*(?P<args>[^)]*)\W*\)\W*{(?P<code>(.|\n)*?)}
```

> [!note] It's impossible to match the nested structures correctly (the code)

