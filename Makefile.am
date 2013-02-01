
AUTOMAKE_OPTIONS = foreign no-dependencies

INCLUDES = @DNETINC@ @EVENTINC@ @PCAPINC@

LDADD = @LIBOBJS@ @DNETLIB@ @EVENTLIB@ @PCAPLIB@

sbin_PROGRAMS = arpd

arpd_SOURCES = arpd.c err.h tree.h

man_MANS = arpd.8

EXTRA_DIST = LICENSE $(man_MANS)

DISTCLEANFILES = *~

