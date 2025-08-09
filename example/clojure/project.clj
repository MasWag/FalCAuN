(def matlab-home (or (System/getenv "MATLAB_HOME")
                     (throw (ex-info "MATLAB_HOME is not set" {}))))
(def sep (System/getProperty "path.separator"))

(def jep-lib (System/getenv "JEP_JAVA_LIBRARY_PATH"))
(def lib-paths (remove nil? [(when matlab-home (str matlab-home "/bin/maca64"))
                             (when matlab-home (str matlab-home "/bin/maci64"))
                             (when matlab-home (str matlab-home "/bin/glnxa64"))
                             jep-lib]))
(def jlp-all (str "-Djava.library.path=" (clojure.string/join sep lib-paths)))

(defproject falcaun-clojure-example "0.1.0-SNAPSHOT"
  :description "Examples to use FalCAuN with Clojure"
  :url "http://github.com/MasWag/FalCAuN.git"
  :license {:name "EPL-2.0 OR GPL-2.0-or-later WITH Classpath-exception-2.0"
            :url "https://www.eclipse.org/legal/epl-2.0/"}
  :dependencies [[org.clojure/clojure "1.11.1"]
                 [net.maswag.falcaun/FalCAuN-core "1.0-SNAPSHOT"]
                 [net.maswag.falcaun/FalCAuN-matlab "1.0-SNAPSHOT"]
                 [net.maswag.falcaun/FalCAuN-python "1.0-SNAPSHOT"]]
  :plugins [[lein-exec "0.3.7"]
            [lein-kibit "0.1.11"]
            [dev.weavejester/lein-cljfmt "0.13.1"]
            [lein-codox "0.10.8"]]
  :source-paths ["src"]
  :codox {:output-path "target/doc"
          :namespaces [falcaun.example.common
                       falcaun.example.auto-trans]
          :metadata {:doc/format :markdown}}
  :jvm-opts ^:replace [~jlp-all]
  :repl-options {:init-ns default.core})
